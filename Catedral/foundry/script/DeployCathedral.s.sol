// SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;

import "forge-std/Script.sol";
import "../../src/ProofOfCoherenceConsensus.sol";

contract DeployCathedralScript is Script {
    function run() public {
        uint256 deployerPrivateKey = vm.envUint("PRIVATE_KEY");

        vm.startBroadcast(deployerPrivateKey);
        ProofOfCoherenceConsensus consensus = new ProofOfCoherenceConsensus(address(0), false);

        bytes32 blockHash = consensus.submitCoherenceBlock(
            "bootstrap-node",
            99_999_900,
            10_000,
            10,
            100,
            keccak256("bootstrap-field")
        );
        vm.stopBroadcast();

        console.log("ProofOfCoherenceConsensus:", address(consensus));
        console.log("Block hash:", uint256(blockHash));
        console.log("Block count:", consensus.blockCount());
    }
}
