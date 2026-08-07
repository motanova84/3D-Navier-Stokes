import { ethers, network } from "hardhat";
import * as fs from "fs";

async function main() {
  console.log(`Deploying PoC MVP on ${network.name}`);

  const [deployer] = await ethers.getSigners();
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

  const deployment = {
    network: network.name,
    chainId: network.config.chainId,
    contract: await consensus.getAddress(),
    deployer: deployer.address,
    blockCount: (await consensus.blockCount()).toString(),
    timestamp: Math.floor(Date.now() / 1000)
  };

  const dir = "deployments";
  if (!fs.existsSync(dir)) fs.mkdirSync(dir);
  fs.writeFileSync(
    `${dir}/hardhat_${network.config.chainId}_poc_mvp.json`,
    JSON.stringify(deployment, null, 2)
  );
}

main().catch(console.error);
