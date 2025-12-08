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

const MINING_PROGRAM_ID = new PublicKey("AxEiL9XDY9R4JVpTTD8m9XvmZnPsncj86jEeBYsJ72qG");
const STAKING_PROGRAM_ID = new PublicKey("8i2AeT3x6vcAw1SwPgTEQJWaqup2JoWqx9V7yh2ZiQ8f");
const TREASURY_PROGRAM_ID = new PublicKey("3YcAbE5r56Ct7QMiEkyhMEPmPYg5aNh7SieYcFbw1eVL");
const TOKEN_PROGRAM_ID = new PublicKey("7d1TQ2HKfzQELVhctnhxwMT6peGrYdXh7SieYcFbw1eVL"); // lode-token
const TOKEN_2022_ID = new PublicKey("TokenzQdBNbLqP5VEhdkAS6EPFLC1PHnBqCXEpPxuEb");

// Instruction discriminators
const INITIALIZE = 0;
const ADVANCE_EPOCH = 1;
const ENTER_EPOCH = 2;
const BUY_HASHRATE = 3;
const CONSUME_RANDOMNESS = 4;
const CREDIT_WINNER = 5;
const CLAIM = 6;
const LIST_HASHRATE = 7;
const BUY_LISTED_HASHRATE = 8;
const CANCEL_LISTING = 9;

// Staking program discriminators
const STAKING_INITIALIZE = 0;
const STAKING_STAKE = 1;

// StakeAccount discriminator
const STAKE_ACCOUNT_DISCRIMINATOR = [0x53, 0x54, 0x41, 0x4B, 0x45, 0x41, 0x43, 0x43]; // "STAKEACC"

function findPda(seeds: Buffer[], programId: PublicKey): [PublicKey, number] {
  return PublicKey.findProgramAddressSync(seeds, programId);
}

async function loadKeypair(path: string): Promise<Keypair> {
  const data = JSON.parse(fs.readFileSync(path, "utf-8"));
  return Keypair.fromSecretKey(Uint8Array.from(data));
}

interface TestUser {
  keypair: Keypair;
  name: string;
  stakeAmount: bigint;
  stakeAccountPda?: PublicKey;
  minerEntryPda?: PublicKey;
}

async function main() {
  const connection = new Connection("http://127.0.0.1:8899", "confirmed");

  // Load payer from default solana CLI config path
  let payer: Keypair;
  const configPath = `${process.env.HOME}/.config/solana/id.json`;

  if (fs.existsSync(configPath)) {
    payer = await loadKeypair(configPath);
    console.log("Loaded keypair from:", configPath);
  } else {
    payer = Keypair.generate();
    console.log("Generated new keypair");
  }

  console.log("Payer:", payer.publicKey.toBase58());

  // Create test users with different stake amounts
  const users: TestUser[] = [
    { keypair: Keypair.generate(), name: "Alice", stakeAmount: 100_000_000_000n }, // 100 LODE
    { keypair: Keypair.generate(), name: "Bob", stakeAmount: 500_000_000_000n },   // 500 LODE
    { keypair: Keypair.generate(), name: "Charlie", stakeAmount: 50_000_000_000n }, // 50 LODE
    { keypair: Keypair.generate(), name: "Diana", stakeAmount: 200_000_000_000n },  // 200 LODE
  ];

  console.log("\n=== Test Users ===");
  for (const user of users) {
    console.log(`  ${user.name}: ${user.keypair.publicKey.toBase58()} (Stake: ${Number(user.stakeAmount) / 1e9} LODE)`);
  }

  // Airdrop SOL to all users
  console.log("\n=== Funding Users ===");
  const airdropPromises = users.map(async (user) => {
    const sig = await connection.requestAirdrop(user.keypair.publicKey, 2 * LAMPORTS_PER_SOL);
    await connection.confirmTransaction(sig);
    console.log(`  ${user.name}: Funded 2 SOL`);
  });
  await Promise.all(airdropPromises);

  // Derive PDAs
  const [configPda] = findPda([Buffer.from("mining_config")], MINING_PROGRAM_ID);
  const [stakingPoolPda] = findPda([Buffer.from("staking_pool")], STAKING_PROGRAM_ID);

  console.log("\n=== Program PDAs ===");
  console.log("  Mining Config:", configPda.toBase58());
  console.log("  Staking Pool:", stakingPoolPda.toBase58());

  // Check if mining program is initialized
  const configInfo = await connection.getAccountInfo(configPda);
  if (!configInfo) {
    console.log("\nMining program not initialized! Run test-mining.ts first.");
    return;
  }

  // Parse config to get current epoch
  const configData = configInfo.data;
  const currentEpoch = configData.readBigUInt64LE(176);
  console.log("\nCurrent Epoch:", currentEpoch.toString());

  // Get current epoch PDA
  const epochIdBuffer = Buffer.alloc(8);
  epochIdBuffer.writeBigUInt64LE(currentEpoch);
  const [epochPda] = findPda([Buffer.from("epoch"), epochIdBuffer], MINING_PROGRAM_ID);

  console.log("Epoch PDA:", epochPda.toBase58());

  // Check epoch status
  const epochInfo = await connection.getAccountInfo(epochPda);
  if (!epochInfo) {
    console.log("Epoch not found!");
    return;
  }

  const epochData = epochInfo.data;
  const endTime = epochData.readBigInt64LE(24);
  const now = Math.floor(Date.now() / 1000);
  const timeRemaining = Number(endTime) - now;

  console.log(`Epoch ends in: ${timeRemaining} seconds`);

  if (timeRemaining <= 0) {
    console.log("\nEpoch has ended! Advancing to new epoch...");
    await advanceEpochIfNeeded(connection, payer, configPda, currentEpoch);
    console.log("\nPlease re-run the script to test with the new epoch.");
    return;
  }

  // Create mock stake accounts for each user
  // Since we need stake accounts for enter_epoch, we'll create them manually
  console.log("\n=== Creating Mock Stake Accounts ===");

  for (const user of users) {
    // Derive stake account PDA
    const [stakeAccountPda, stakeAccountBump] = findPda(
      [Buffer.from("stake_account"), user.keypair.publicKey.toBuffer()],
      STAKING_PROGRAM_ID
    );
    user.stakeAccountPda = stakeAccountPda;

    // Derive miner entry PDA
    const [minerEntryPda] = findPda(
      [Buffer.from("miner_entry"), user.keypair.publicKey.toBuffer()],
      MINING_PROGRAM_ID
    );
    user.minerEntryPda = minerEntryPda;

    // Check if stake account exists
    const stakeAccountInfo = await connection.getAccountInfo(stakeAccountPda);

    if (!stakeAccountInfo) {
      // Create mock stake account
      // StakeAccount layout:
      //   discriminator (8):    0..8
      //   owner (32):           8..40
      //   pool (32):            40..72
      //   amount (8):           72..80
      //   stake_timestamp (8):  80..88
      //   pending_rewards (8):  88..96
      //   bump (1):             96..97
      //   padding (7):          97..104

      const stakeAccountSize = 104;
      const lamports = await connection.getMinimumBalanceForRentExemption(stakeAccountSize);

      // We need to create the account owned by the staking program
      // Since we can't sign as the staking program PDA, we'll use a workaround:
      // Create as system account first, then have staking program own it
      // For testing, we'll create a mock account with the right data

      console.log(`  Creating mock stake account for ${user.name}...`);

      // Create a simple account with mock stake data
      // In real scenario, user would call staking program's stake instruction
      const mockStakeData = Buffer.alloc(stakeAccountSize);

      // Write discriminator
      Buffer.from(STAKE_ACCOUNT_DISCRIMINATOR).copy(mockStakeData, 0);

      // Write owner (user pubkey)
      user.keypair.publicKey.toBuffer().copy(mockStakeData, 8);

      // Write pool (staking pool PDA)
      stakingPoolPda.toBuffer().copy(mockStakeData, 40);

      // Write amount
      mockStakeData.writeBigUInt64LE(user.stakeAmount, 72);

      // Write stake_timestamp (30 days ago for time multiplier bonus)
      const thirtyDaysAgo = BigInt(Math.floor(Date.now() / 1000) - 30 * 24 * 60 * 60);
      mockStakeData.writeBigInt64LE(thirtyDaysAgo, 80);

      // Write pending_rewards
      mockStakeData.writeBigUInt64LE(0n, 88);

      // Write bump
      mockStakeData[96] = stakeAccountBump;

      // For testing, we'll create the account directly using system program
      // and have payer fund it. The account will have wrong owner (system) but
      // we can test the data parsing.

      // Actually, let's create a real approach: use the staking program's initialize if pool doesn't exist
      // For now, let's skip stake account creation and test what we can

      console.log(`    Stake Account PDA: ${stakeAccountPda.toBase58()}`);
      console.log(`    Note: Mock stake accounts need staking program to create them properly`);
    } else {
      console.log(`  ${user.name}: Stake account exists at ${stakeAccountPda.toBase58()}`);
    }

    console.log(`  Miner Entry PDA: ${minerEntryPda.toBase58()}`);
  }

  // Since enter_epoch requires real stake accounts owned by staking program,
  // let's test what we can: display the current epoch state and instructions

  console.log("\n=== Current Epoch State ===");
  const id = epochData.readBigUInt64LE(8);
  const startTime = epochData.readBigInt64LE(16);
  const lotteryPool = epochData.readBigUInt64LE(32);
  const emissionPool = epochData.readBigUInt64LE(40);
  const totalHashrateLow = epochData.readBigUInt64LE(48);
  const participantCount = epochData.readBigUInt64LE(96);

  console.log(`  ID: ${id}`);
  console.log(`  Start: ${new Date(Number(startTime) * 1000).toISOString()}`);
  console.log(`  End: ${new Date(Number(endTime) * 1000).toISOString()}`);
  console.log(`  Time Remaining: ${timeRemaining}s`);
  console.log(`  Lottery Pool: ${Number(lotteryPool) / 1e9} LODE`);
  console.log(`  Emission Pool: ${Number(emissionPool) / 1e9} LODE`);
  console.log(`  Total Hashrate: ${totalHashrateLow}`);
  console.log(`  Participants: ${participantCount}`);

  console.log("\n=== Next Steps ===");
  console.log("To properly test multi-user mining, we need:");
  console.log("1. Initialize the staking program (if not done)");
  console.log("2. Have each user stake LODE via the staking program");
  console.log("3. Then each user can call enter_epoch with their stake account");
  console.log("4. Users can optionally call buy_hashrate to boost their odds");
  console.log("5. After epoch ends, call consume_randomness to select winners");
  console.log("6. Call credit_winner for each winner to allocate rewards");
  console.log("7. Winners call claim to receive their LODE");

  // Print instruction layouts for reference
  console.log("\n=== Instruction Reference ===");
  console.log("EnterEpoch accounts:");
  console.log("  0. [signer, writable] User");
  console.log("  1. [] Mining config PDA");
  console.log("  2. [writable] Current epoch PDA");
  console.log("  3. [writable] Miner entry PDA");
  console.log("  4. [] User's stake account (from staking program)");
  console.log("  5. [] System program");

  console.log("\nBuyHashrate accounts:");
  console.log("  0. [signer] User");
  console.log("  1. [] Mining config PDA");
  console.log("  2. [writable] Current epoch PDA");
  console.log("  3. [writable] User's miner entry");
  console.log("  4. [writable] User's LODE token account");
  console.log("  5. [writable] LODE mint");
  console.log("  6. [] Token-2022 program");
  console.log("  Data: amount (u64)");
}

async function advanceEpochIfNeeded(
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
    data: Buffer.from([ADVANCE_EPOCH]),
  });

  try {
    const tx = new Transaction().add(advanceIx);
    const { blockhash } = await connection.getLatestBlockhash("finalized");
    tx.recentBlockhash = blockhash;
    tx.feePayer = payer.publicKey;

    const sig = await sendAndConfirmTransaction(connection, tx, [payer], {
      commitment: "confirmed",
      maxRetries: 5,
    });
    console.log("Advanced to epoch", nextEpochId.toString(), "- Sig:", sig);
    return true;
  } catch (e: any) {
    console.error("Advance epoch failed:", e.message);
    return false;
  }
}

main().catch(console.error);
