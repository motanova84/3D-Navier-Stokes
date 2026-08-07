// SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;

interface IZKCoherenceVerifier {
    function verifyProof(
        uint256[2] calldata a,
        uint256[2][2] calldata b,
        uint256[2] calldata c,
        uint256[2] calldata publicInputs
    ) external view returns (bool);
}

contract ProofOfCoherenceConsensus {
    uint64 public constant COHERENCE_THRESHOLD = 99_999_900; // 0.999999 * 1e8
    uint32 public constant MAX_VON_NEUMANN_ENTROPY = 10_000; // 0.0100 * 1e6
    uint32 public constant MIN_STEP_COUNT = 100;

    struct CoherenceState {
        uint64 coherencePsi;
        uint32 vonNeumannEntropy;
        uint32 harmonicDispersion;
        uint32 stepCount;
        uint16 reservedWaterMetricA; // Reserved for Water Trinity metric (scaled 0-1000)
        uint16 reservedWaterMetricB; // Reserved for Water Trinity metric (scaled 0-1000)
    }

    struct PoCBlock {
        uint64 blockId;
        uint64 timestamp;
        address validator;
        bytes32 nodeIdHash;
        bytes32 fieldHashPsi;
        bytes32 stateHash;
        CoherenceState state;
    }

    address public owner;
    uint64 public blockCount;
    bytes32 public latestBlockHash;
    mapping(uint64 => PoCBlock) private blocks;
    mapping(bytes32 => bool) public validatedWavefunctions;

    IZKCoherenceVerifier public zkVerifier;
    bool public zkValidationEnabled;

    event CoherenceBlockSubmitted(
        uint64 indexed blockId,
        address indexed validator,
        bytes32 indexed fieldHashPsi,
        bytes32 stateHash,
        bytes32 nodeIdHash,
        uint64 coherencePsi,
        uint32 vonNeumannEntropy,
        uint32 stepCount
    );

    event ZKVerifierUpdated(address indexed verifier, bool enabled);
    event WavefunctionValidated(bytes32 indexed fieldHashPsi, bool indexed valid);
    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    modifier onlyOwner() {
        require(msg.sender == owner, "PoC: solo owner");
        _;
    }

    constructor(address verifier, bool zkEnabled) {
        if (zkEnabled) {
            require(verifier != address(0), "PoC: verificador no configurado");
        }
        owner = msg.sender;
        emit OwnershipTransferred(address(0), msg.sender);
        zkVerifier = IZKCoherenceVerifier(verifier);
        zkValidationEnabled = zkEnabled;
        latestBlockHash = keccak256(abi.encodePacked("QCAL_POC_GENESIS_141.7001HZ"));
    }


    function transferOwnership(address newOwner) external onlyOwner {
        require(newOwner != address(0), "PoC: owner invalido");
        emit OwnershipTransferred(owner, newOwner);
        owner = newOwner;
    }

    function setZKVerifier(address verifier) external onlyOwner {
        require(verifier != address(0), "PoC: verificador no configurado");
        zkVerifier = IZKCoherenceVerifier(verifier);
        emit ZKVerifierUpdated(verifier, zkValidationEnabled);
    }

    function setZKValidationEnabled(bool enabled) external onlyOwner {
        if (enabled) {
            require(address(zkVerifier) != address(0), "PoC: verificador no configurado");
        }
        zkValidationEnabled = enabled;
        emit ZKVerifierUpdated(address(zkVerifier), enabled);
    }

    function getBlock(uint64 blockId) external view returns (PoCBlock memory) {
        require(blockId > 0 && blockId <= blockCount, "PoC: bloque inexistente");
        return blocks[blockId];
    }

    function submitCoherenceBlock(
        string calldata nodeId,
        uint64 coherencePsi,
        uint32 vonNeumannEntropy,
        uint32 harmonicDispersion,
        uint32 stepCount,
        bytes32 fieldHashPsi
    ) external returns (bytes32) {
        return _submitCoherenceBlock(
            nodeId,
            coherencePsi,
            vonNeumannEntropy,
            harmonicDispersion,
            stepCount,
            fieldHashPsi
        );
    }

    function submitCoherenceBlockWithZK(
        string calldata nodeId,
        uint64 coherencePsi,
        uint32 vonNeumannEntropy,
        uint32 harmonicDispersion,
        uint32 stepCount,
        bytes32 fieldHashPsi,
        uint256[2] calldata a,
        uint256[2][2] calldata b,
        uint256[2] calldata c
    ) external returns (bytes32) {
        require(zkValidationEnabled, "PoC: ZK deshabilitado");
        require(address(zkVerifier) != address(0), "PoC: verificador no configurado");

        // Public inputs are derived on-chain to bind proof acceptance to
        // the submitted spectral hash and canonical coherence threshold.
        uint256[2] memory publicInputs = [
            uint256(fieldHashPsi),
            uint256(COHERENCE_THRESHOLD)
        ];

        bool valid = zkVerifier.verifyProof(a, b, c, publicInputs);
        require(valid, "PoC: prueba ZK invalida");

        validatedWavefunctions[fieldHashPsi] = true;
        emit WavefunctionValidated(fieldHashPsi, true);

        return _submitCoherenceBlock(
            nodeId,
            coherencePsi,
            vonNeumannEntropy,
            harmonicDispersion,
            stepCount,
            fieldHashPsi
        );
    }

    function _submitCoherenceBlock(
        string calldata nodeId,
        uint64 coherencePsi,
        uint32 vonNeumannEntropy,
        uint32 harmonicDispersion,
        uint32 stepCount,
        bytes32 fieldHashPsi
    ) internal returns (bytes32) {
        require(bytes(nodeId).length > 0, "PoC: nodeId vacio");
        require(coherencePsi >= COHERENCE_THRESHOLD, "PoC: Coherencia insuficiente");
        require(vonNeumannEntropy <= MAX_VON_NEUMANN_ENTROPY, "PoC: Entropia fuera de limite");
        require(stepCount >= MIN_STEP_COUNT, "PoC: Ventana inestable");

        require(blockCount < type(uint64).max, "PoC: limite de bloques alcanzado");
        uint64 newBlockId = blockCount + 1;
        bytes32 nodeIdHash = keccak256(bytes(nodeId));

        bytes32 blockHash = keccak256(
            abi.encodePacked(
                newBlockId,
                uint64(block.timestamp),
                msg.sender,
                nodeIdHash,
                fieldHashPsi,
                coherencePsi,
                vonNeumannEntropy,
                harmonicDispersion,
                stepCount,
                latestBlockHash
            )
        );

        blocks[newBlockId] = PoCBlock({
            blockId: newBlockId,
            timestamp: uint64(block.timestamp),
            validator: msg.sender,
            nodeIdHash: nodeIdHash,
            fieldHashPsi: fieldHashPsi,
            stateHash: blockHash,
            state: CoherenceState({
                coherencePsi: coherencePsi,
                vonNeumannEntropy: vonNeumannEntropy,
                harmonicDispersion: harmonicDispersion,
                stepCount: stepCount,
                reservedWaterMetricA: 0,
                reservedWaterMetricB: 0
            })
        });

        blockCount = newBlockId;
        latestBlockHash = blockHash;

        emit CoherenceBlockSubmitted(
            newBlockId,
            msg.sender,
            fieldHashPsi,
            blockHash,
            nodeIdHash,
            coherencePsi,
            vonNeumannEntropy,
            stepCount
        );

        return blockHash;
    }
}
