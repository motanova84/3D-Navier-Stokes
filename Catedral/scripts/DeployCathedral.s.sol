// SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;

import "forge-std/Script.sol";
import "../src/ProofOfCoherenceConsensus.sol";

contract DeployCathedral is Script {
    function run() external {
        uint256 pk = vm.envUint("PRIVATE_KEY");

        vm.startBroadcast(pk);
        ProofOfCoherenceConsensus consensus = new ProofOfCoherenceConsensus(address(0), false);

        // Genesis anchor for deterministic PoC chain initialization
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
        console.log("Genesis anchored block hash:", uint256(blockHash));
        console.log("Block count:", consensus.blockCount());
    }
}
