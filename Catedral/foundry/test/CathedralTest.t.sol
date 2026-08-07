// SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;

import "forge-std/Test.sol";
import "../../src/ProofOfCoherenceConsensus.sol";

contract MockZKVerifier is IZKCoherenceVerifier {
    bool public result;

    constructor(bool _result) {
        result = _result;
    }

    function setResult(bool _result) external {
        result = _result;
    }

    function verifyProof(
        uint256[2] calldata,
        uint256[2][2] calldata,
        uint256[2] calldata,
        uint256[2] calldata
    ) external view returns (bool) {
        return result;
    }
}

contract CathedralTest is Test {
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

    event WavefunctionValidated(bytes32 indexed fieldHashPsi, bool indexed valid);

    ProofOfCoherenceConsensus public consensus;
    MockZKVerifier public verifier;

    function setUp() public {
        verifier = new MockZKVerifier(true);
        consensus = new ProofOfCoherenceConsensus(address(verifier), false);
    }

    function testSubmitCoherenceBlockStoresStateAndIncrementsCounter() public {
        vm.warp(1_700_000_000);
        bytes32 fieldHash = keccak256("psi-1");
        bytes32 returnedHash = consensus.submitCoherenceBlock(
            "node-a",
            99_999_900,
            10_000,
            10,
            100,
            fieldHash
        );

        assertEq(consensus.blockCount(), 1);
        assertEq(consensus.latestBlockHash(), returnedHash);

        ProofOfCoherenceConsensus.PoCBlock memory blockData = consensus.getBlock(1);
        assertEq(blockData.blockId, 1);
        assertEq(blockData.timestamp, 1_700_000_000);
        assertEq(blockData.validator, address(this));
        assertEq(blockData.fieldHashPsi, fieldHash);
        assertEq(blockData.nodeIdHash, keccak256(bytes("node-a")));
        assertEq(blockData.state.coherencePsi, 99_999_900);
        assertEq(blockData.state.vonNeumannEntropy, 10_000);
        assertEq(blockData.state.harmonicDispersion, 10);
        assertEq(blockData.state.stepCount, 100);
    }

    function testSubmitCoherenceBlockEmitsEvent() public {
        vm.warp(1_700_000_100);
        bytes32 fieldHash = keccak256("psi-event");
        bytes32 genesisHash = consensus.latestBlockHash();
        bytes32 nodeIdHash = keccak256(bytes("node-e"));

        bytes32 expectedHash = keccak256(
            abi.encodePacked(
                uint64(1),
                uint64(1_700_000_100),
                address(this),
                nodeIdHash,
                fieldHash,
                uint64(99_999_900),
                uint32(10_000),
                uint32(10),
                uint32(100),
                genesisHash
            )
        );

        vm.expectEmit(true, true, true, true);
        emit CoherenceBlockSubmitted(
            1,
            address(this),
            fieldHash,
            expectedHash,
            nodeIdHash,
            99_999_900,
            10_000,
            100
        );

        bytes32 stored = consensus.submitCoherenceBlock(
            "node-e",
            99_999_900,
            10_000,
            10,
            100,
            fieldHash
        );

        assertEq(stored, expectedHash);
    }

    function testSubmitCoherenceBlockRevertsLowCoherence() public {
        vm.expectRevert("PoC: Coherencia insuficiente");
        consensus.submitCoherenceBlock("node-a", 99_999_899, 10_000, 10, 100, keccak256("psi-low"));
    }

    function testSubmitCoherenceBlockRevertsHighEntropy() public {
        vm.expectRevert("PoC: Entropia fuera de limite");
        consensus.submitCoherenceBlock("node-a", 99_999_900, 10_001, 10, 100, keccak256("psi-high-entropy"));
    }

    function testSubmitCoherenceBlockRevertsLowSteps() public {
        vm.expectRevert("PoC: Ventana inestable");
        consensus.submitCoherenceBlock("node-a", 99_999_900, 10_000, 10, 99, keccak256("psi-low-steps"));
    }

    function testHashChainingAcrossBlocks() public {
        vm.warp(1_700_000_000);
        bytes32 first = consensus.submitCoherenceBlock(
            "node-a",
            99_999_900,
            10_000,
            11,
            100,
            keccak256("psi-1")
        );

        vm.warp(1_700_000_010);
        bytes32 second = consensus.submitCoherenceBlock(
            "node-b",
            99_999_901,
            9_999,
            12,
            101,
            keccak256("psi-2")
        );

        ProofOfCoherenceConsensus.PoCBlock memory secondBlock = consensus.getBlock(2);
        bytes32 expectedSecond = keccak256(
            abi.encodePacked(
                uint64(2),
                uint64(1_700_000_010),
                address(this),
                keccak256(bytes("node-b")),
                keccak256("psi-2"),
                uint64(99_999_901),
                uint32(9_999),
                uint32(12),
                uint32(101),
                first
            )
        );

        assertEq(secondBlock.stateHash, second);
        assertEq(secondBlock.stateHash, expectedSecond);
        assertEq(consensus.latestBlockHash(), second);
    }

    function testSubmitCoherenceBlockWithZKDisabledReverts() public {
        uint256[2] memory a;
        uint256[2][2] memory b;
        uint256[2] memory c;

        vm.expectRevert("PoC: ZK deshabilitado");
        consensus.submitCoherenceBlockWithZK(
            "node-zk",
            99_999_900,
            10_000,
            10,
            100,
            keccak256("psi-zk"),
            a,
            b,
            c
        );
    }

    function testSubmitCoherenceBlockWithZKValidatesAndStoresWavefunction() public {
        consensus.setZKValidationEnabled(true);

        uint256[2] memory a;
        uint256[2][2] memory b;
        uint256[2] memory c;
        bytes32 fieldHash = keccak256("psi-zk-valid");

        vm.expectEmit(true, true, false, false);
        emit WavefunctionValidated(fieldHash, true);

        bytes32 stateHash = consensus.submitCoherenceBlockWithZK(
            "node-zk",
            99_999_900,
            10_000,
            10,
            100,
            fieldHash,
            a,
            b,
            c
        );

        assertTrue(consensus.validatedWavefunctions(fieldHash));
        assertEq(consensus.blockCount(), 1);
        assertEq(consensus.latestBlockHash(), stateHash);
    }

    function testSubmitCoherenceBlockWithZKInvalidProofReverts() public {
        consensus.setZKValidationEnabled(true);
        verifier.setResult(false);

        uint256[2] memory a;
        uint256[2][2] memory b;
        uint256[2] memory c;

        vm.expectRevert("PoC: prueba ZK invalida");
        consensus.submitCoherenceBlockWithZK(
            "node-zk",
            99_999_900,
            10_000,
            10,
            100,
            keccak256("psi-zk-invalid"),
            a,
            b,
            c
        );
    }
}
