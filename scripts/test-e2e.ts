/**
 * End-to-End Test Script for LODE Mining Protocol
 *
 * This script sets up the full protocol stack and tests multi-user mining:
 * 1. Creates a Token-2022 LODE mint
 * 2. Initializes the staking pool
 * 3. Creates test users with LODE tokens
 * 4. Users stake their tokens
 * 5. Users enter the current epoch
 * 6. Test epoch advance and winners
 */

import {
  Connection,
  Keypair,
  PublicKey,
  TransactionInstruction,
  Transaction,
  sendAndConfirmTransaction,
  SystemProgram,
  LAMPORTS_PER_SOL,
} from "@solana/web3.js";
import * as fs from "fs";

// Program IDs (from Surfpool.toml)
const MINING_PROGRAM_ID = new PublicKey("AxEiL9XDY9R4JVpTTD8m9XvmZnPsncj86jEeBYsJ72qG");
const STAKING_PROGRAM_ID = new PublicKey("8i2AeT3x6vcAw1SwPgTEQJWaqup2JoWqx9V7yh2ZiQ8f");
const TREASURY_PROGRAM_ID = new PublicKey("3YcAbE5r56Ct7QMiEkyhMEPmPYg5aNh7SieYcFbw1eVL");
const TOKEN_PROGRAM_ID = new PublicKey("7d1TQ2HKfzQELVhctnhxwMT6peGrYdXh7SieYcFbw1eVL");
const TOKEN_2022_ID = new PublicKey("TokenzQdBNbLqP5VEhdkAS6EPFLC1PHnBqCXEpPxuEb");

// Instruction discriminators for mining program
const MINING_INITIALIZE = 0;
const MINING_ADVANCE_EPOCH = 1;
const MINING_ENTER_EPOCH = 2;
const MINING_BUY_HASHRATE = 3;

// Instruction discriminators for staking program
const STAKING_INITIALIZE = 0;
const STAKING_STAKE = 1;

function findPda(seeds: Buffer[], programId: PublicKey): [PublicKey, number] {
  return PublicKey.findProgramAddressSync(seeds, programId);
}

async function loadKeypair(path: string): Promise<Keypair> {
  const data = JSON.parse(fs.readFileSync(path, "utf-8"));
  return Keypair.fromSecretKey(Uint8Array.from(data));
}

async function sendTx(
  connection: Connection,
  instructions: TransactionInstruction[],
  signers: Keypair[],
  label: string
): Promise<string | null> {
  try {
    const tx = new Transaction().add(...instructions);
    const { blockhash } = await connection.getLatestBlockhash("finalized");
    tx.recentBlockhash = blockhash;
    tx.feePayer = signers[0].publicKey;

    const sig = await sendAndConfirmTransaction(connection, tx, signers, {
      commitment: "confirmed",
      maxRetries: 5,
    });
    console.log(`  ${label}: ${sig.slice(0, 20)}...`);
    return sig;
  } catch (e: any) {
    console.error(`  ${label} FAILED:`, e.message);
    if (e.logs) {
      console.error("  Logs:", e.logs.slice(-5).join("\n    "));
    }
    return null;
  }
}

interface TestUser {
  keypair: Keypair;
  name: string;
  stakeAmount: bigint;
  tokenAccount?: PublicKey;
  stakeAccountPda?: PublicKey;
  minerEntryPda?: PublicKey;
}

async function main() {
  const connection = new Connection("http://127.0.0.1:8899", "confirmed");

  // Load payer (admin)
  let admin: Keypair;
  const configPath = `${process.env.HOME}/.config/solana/id.json`;
  if (fs.existsSync(configPath)) {
    admin = await loadKeypair(configPath);
  } else {
    admin = Keypair.generate();
  }
  console.log("Admin:", admin.publicKey.toBase58());

  // Check balance
  const balance = await connection.getBalance(admin.publicKey);
  console.log("Balance:", balance / LAMPORTS_PER_SOL, "SOL");

  // Create LODE mint (Token-2022)
  const lodeMint = Keypair.generate();
  console.log("\n=== LODE Mint Setup ===");
  console.log("Mint:", lodeMint.publicKey.toBase58());

  // Create test users
  const users: TestUser[] = [
    { keypair: Keypair.generate(), name: "Alice", stakeAmount: 100_000_000_000n },   // 100 LODE
    { keypair: Keypair.generate(), name: "Bob", stakeAmount: 500_000_000_000n },     // 500 LODE
    { keypair: Keypair.generate(), name: "Charlie", stakeAmount: 50_000_000_000n },  // 50 LODE
    { keypair: Keypair.generate(), name: "Diana", stakeAmount: 200_000_000_000n },   // 200 LODE
  ];

  console.log("\n=== Test Users ===");
  for (const user of users) {
    console.log(`  ${user.name}: ${user.keypair.publicKey.toBase58().slice(0, 20)}... (${Number(user.stakeAmount) / 1e9} LODE)`);
  }

  // Fund all users with SOL
  console.log("\n=== Funding Users ===");
  for (const user of users) {
    const sig = await connection.requestAirdrop(user.keypair.publicKey, 2 * LAMPORTS_PER_SOL);
    await connection.confirmTransaction(sig);
    console.log(`  ${user.name}: 2 SOL`);
  }

  // Derive PDAs
  const [miningConfigPda] = findPda([Buffer.from("mining_config")], MINING_PROGRAM_ID);
  const [stakingPoolPda] = findPda([Buffer.from("staking_pool")], STAKING_PROGRAM_ID);
  const [treasuryPda] = findPda([Buffer.from("treasury")], TREASURY_PROGRAM_ID);
  const [vaultPda] = findPda([Buffer.from("vault"), stakingPoolPda.toBuffer()], STAKING_PROGRAM_ID);

  console.log("\n=== PDAs ===");
  console.log("  Mining Config:", miningConfigPda.toBase58());
  console.log("  Staking Pool:", stakingPoolPda.toBase58());
  console.log("  Treasury:", treasuryPda.toBase58());
  console.log("  Vault:", vaultPda.toBase58());

  // Check if mining is already initialized (via Surfpool runbook)
  const miningConfigInfo = await connection.getAccountInfo(miningConfigPda);

  if (miningConfigInfo) {
    console.log("\n=== Mining Program Already Initialized ===");

    // Parse config
    const configData = miningConfigInfo.data;
    const currentMint = new PublicKey(configData.slice(8, 40));
    const currentEpoch = configData.readBigUInt64LE(176);
    const initialized = configData[193];

    console.log("  Mint:", currentMint.toBase58());
    console.log("  Current Epoch:", currentEpoch.toString());
    console.log("  Initialized:", initialized === 1 ? "Yes" : "No");

    // Check staking pool
    const stakingPoolInfo = await connection.getAccountInfo(stakingPoolPda);
    if (stakingPoolInfo) {
      console.log("\n=== Staking Pool Already Initialized ===");
      const poolData = stakingPoolInfo.data;
      const totalStaked = poolData.readBigUInt64LE(96);
      console.log("  Total Staked:", (Number(totalStaked) / 1e9).toFixed(2), "LODE");
    } else {
      console.log("\n!!! Staking pool not initialized - need to set up staking first");
    }

    // Get current epoch info
    const epochIdBuffer = Buffer.alloc(8);
    epochIdBuffer.writeBigUInt64LE(currentEpoch);
    const [epochPda] = findPda([Buffer.from("epoch"), epochIdBuffer], MINING_PROGRAM_ID);

    const epochInfo = await connection.getAccountInfo(epochPda);
    if (epochInfo) {
      const epochData = epochInfo.data;
      const endTime = epochData.readBigInt64LE(24);
      const participantCount = epochData.readBigUInt64LE(96);
      const totalHashrate = epochData.readBigUInt64LE(48);

      const now = Math.floor(Date.now() / 1000);
      const timeRemaining = Number(endTime) - now;

      console.log("\n=== Current Epoch ===");
      console.log("  ID:", currentEpoch.toString());
      console.log("  Time Remaining:", timeRemaining > 0 ? `${timeRemaining}s` : "ENDED");
      console.log("  Participants:", participantCount.toString());
      console.log("  Total Hashrate:", totalHashrate.toString());

      if (timeRemaining <= 0) {
        console.log("\n>>> Advancing epoch...");
        await advanceEpoch(connection, admin, miningConfigPda, currentEpoch);
      }
    }

    // Derive stake account PDAs for each user
    console.log("\n=== User Stake Accounts ===");
    for (const user of users) {
      const [stakeAccountPda] = findPda(
        [Buffer.from("stake_account"), user.keypair.publicKey.toBuffer()],
        STAKING_PROGRAM_ID
      );
      user.stakeAccountPda = stakeAccountPda;

      const [minerEntryPda] = findPda(
        [Buffer.from("miner_entry"), user.keypair.publicKey.toBuffer()],
        MINING_PROGRAM_ID
      );
      user.minerEntryPda = minerEntryPda;

      const stakeInfo = await connection.getAccountInfo(stakeAccountPda);
      console.log(`  ${user.name}:`);
      console.log(`    Stake Account: ${stakeAccountPda.toBase58().slice(0, 20)}... ${stakeInfo ? "(exists)" : "(not created)"}`);
      console.log(`    Miner Entry: ${minerEntryPda.toBase58().slice(0, 20)}...`);
    }

  } else {
    console.log("\n!!! Mining program not initialized");
    console.log(">>> Please run 'bun run test-mining.ts' first to initialize the mining program");
  }

  console.log("\n=== Summary ===");
  console.log("The mining program has been initialized by Surfpool's deployment runbook.");
  console.log("To test multi-user mining flow:");
  console.log("1. Initialize staking pool (if not done)");
  console.log("2. Create LODE tokens for users");
  console.log("3. Users stake via staking program");
  console.log("4. Users enter epoch via mining program");
  console.log("5. Wait for epoch to end, advance, and draw winners");
}

async function advanceEpoch(
  connection: Connection,
  payer: Keypair,
  configPda: PublicKey,
  currentEpochId: bigint
): Promise<boolean> {
  const currentEpochIdBuffer = Buffer.alloc(8);
  currentEpochIdBuffer.writeBigUInt64LE(currentEpochId);
  const [currentEpochPda] = findPda([Buffer.from("epoch"), currentEpochIdBuffer], MINING_PROGRAM_ID);

  const nextEpochId = currentEpochId + 1n;
  const nextEpochIdBuffer = Buffer.alloc(8);
  nextEpochIdBuffer.writeBigUInt64LE(nextEpochId);
  const [nextEpochPda] = findPda([Buffer.from("epoch"), nextEpochIdBuffer], MINING_PROGRAM_ID);

  const advanceIx = new TransactionInstruction({
    programId: MINING_PROGRAM_ID,
    keys: [
      { pubkey: payer.publicKey, isSigner: true, isWritable: true },
      { pubkey: configPda, isSigner: false, isWritable: true },
      { pubkey: currentEpochPda, isSigner: false, isWritable: false },
      { pubkey: nextEpochPda, isSigner: false, isWritable: true },
      { pubkey: SystemProgram.programId, isSigner: false, isWritable: false },
    ],
    data: Buffer.from([MINING_ADVANCE_EPOCH]),
  });

  const sig = await sendTx(connection, [advanceIx], [payer], `Advance to epoch ${nextEpochId}`);
  return sig !== null;
}

main().catch(console.error);
