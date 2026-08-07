import { ethers, network } from "hardhat";

async function main() {
  const [deployer] = await ethers.getSigners();
  console.log("Deploying ProofOfCoherenceConsensus");
  console.log(`Network: ${network.name}`);
  console.log(`Deployer: ${deployer.address}`);

  const Factory = await ethers.getContractFactory("ProofOfCoherenceConsensus");
  const consensus = await Factory.deploy(ethers.ZeroAddress, false);
  await consensus.waitForDeployment();

  const tx = await consensus.submitCoherenceBlock(
    "bootstrap-node",
    99_999_900,
    10_000,
    10,
    100,
    ethers.keccak256(ethers.toUtf8Bytes("bootstrap-field"))
  );
  await tx.wait();

  console.log(`Contract: ${await consensus.getAddress()}`);
  console.log(`Block count: ${await consensus.blockCount()}`);
}

main().catch(console.error);
