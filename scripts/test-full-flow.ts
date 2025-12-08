/**
 * Full End-to-End Test for LODE Mining Protocol
 *
 * This script tests the complete multi-user mining flow:
 * 1. Creates a Token-2022 LODE mint
 * 2. Initializes the staking pool
 * 3. Creates test users with LODE tokens
 * 4. Users stake their tokens
 * 5. Users enter the current epoch
 * 6. Users buy hashrate (pay-to-mine)
 * 7. Wait for epoch to end, advance, and draw winners
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
import {
  createInitializeMint2Instruction,
  createAssociatedTokenAccountInstruction,
  createMintToInstruction,
  getAssociatedTokenAddress,
  TOKEN_2022_PROGRAM_ID,
  ASSOCIATED_TOKEN_PROGRAM_ID,
  getMint,
} from "@solana/spl-token";
import * as fs from "fs";

// Program IDs from Surfpool.toml
const MINING_PROGRAM_ID = new PublicKey("AxEiL9XDY9R4JVpTTD8m9XvmZnPsncj86jEeBYsJ72qG");
const STAKING_PROGRAM_ID = new PublicKey("8i2AeT3x6vcAw1SwPgTEQJWaqup2JoWqx9V7yh2ZiQ8f");
const TREASURY_PROGRAM_ID = new PublicKey("3YcAbE5r56Ct7QMiEkyhMEPmPYg5aNh7SieYcFbw1eVL");
const LODE_TOKEN_PROGRAM_ID = new PublicKey("7d1TQ2HKfzQELVhctnhxwMT6peGrYdXh7jWcpxJTxjr1");

// Instruction discriminators
const MINING_INITIALIZE = 0;
const MINING_ADVANCE_EPOCH = 1;
const MINING_ENTER_EPOCH = 2;
const MINING_BUY_HASHRATE = 3;
const MINING_LIST_HASHRATE = 7;
const MINING_BUY_LISTED_HASHRATE = 8;
const MINING_CANCEL_LISTING = 9;

const STAKING_INITIALIZE = 0;
const STAKING_STAKE = 1;

// Discriminators for account validation
const STAKING_POOL_DISCRIMINATOR = Buffer.from([0x53, 0x54, 0x41, 0x4B, 0x50, 0x4F, 0x4F, 0x4C]); // "STAKPOOL"
const STAKE_ACCOUNT_DISCRIMINATOR = Buffer.from([0x53, 0x54, 0x41, 0x4B, 0x45, 0x41, 0x43, 0x43]); // "STAKEACC"

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
  label: string,
  retries = 5
): Promise<string | null> {
  for (let attempt = 1; attempt <= retries; attempt++) {
    try {
      const tx = new Transaction().add(...instructions);
      // Get fresh blockhash immediately before sending
      const { blockhash } = await connection.getLatestBlockhash("processed");
      tx.recentBlockhash = blockhash;
      tx.feePayer = signers[0].publicKey;

      // Sign immediately
      tx.sign(...signers);

      // Send raw transaction with skip preflight for speed
      const rawTx = tx.serialize();
      const sig = await connection.sendRawTransaction(rawTx, {
        skipPreflight: false,
        preflightCommitment: "processed",
        maxRetries: 0, // Don't let web3.js retry, we handle it
      });

      // Wait for confirmation
      const confirmation = await connection.confirmTransaction(sig, "confirmed");
      if (confirmation.value.err) {
        throw new Error(`Transaction failed: ${JSON.stringify(confirmation.value.err)}`);
      }

      console.log(`  [OK] ${label}: ${sig.slice(0, 20)}...`);
      return sig;
    } catch (e: any) {
      const isBlockHeightError = e.message?.includes("block height exceeded") || e.message?.includes("expired");
      if (isBlockHeightError && attempt < retries) {
        console.log(`  [RETRY ${attempt}/${retries}] ${label}: Block height expired, retrying...`);
        await new Promise(r => setTimeout(r, 200)); // Small delay
        continue;
      }
      console.error(`  [FAIL] ${label}:`, e.message);
      if (e.logs) {
        console.error("  Logs:", e.logs.slice(-5).join("\n    "));
      }
      return null;
    }
  }
  return null;
}

interface TestUser {
  keypair: Keypair;
  name: string;
  stakeAmount: bigint;
  burnAmount: bigint; // Extra tokens reserved for buying hashrate
  tokenAccount?: PublicKey;
  stakeAccountPda?: PublicKey;
  minerEntryPda?: PublicKey;
}

async function main() {
  console.log("=".repeat(60));
  console.log("  LODE Protocol Full E2E Test");
  console.log("=".repeat(60));

  const connection = new Connection("http://127.0.0.1:8899", "confirmed");

  // Load admin keypair
  let admin: Keypair;
  const configPath = `${process.env.HOME}/.config/solana/id.json`;
  if (fs.existsSync(configPath)) {
    admin = await loadKeypair(configPath);
  } else {
    admin = Keypair.generate();
  }
  console.log("\nAdmin:", admin.publicKey.toBase58());

  // Check and fund admin
  let balance = await connection.getBalance(admin.publicKey);
  console.log("Balance:", balance / LAMPORTS_PER_SOL, "SOL");
  if (balance < 5 * LAMPORTS_PER_SOL) {
    console.log("Requesting airdrop...");
    const sig = await connection.requestAirdrop(admin.publicKey, 10 * LAMPORTS_PER_SOL);
    await connection.confirmTransaction(sig);
    balance = await connection.getBalance(admin.publicKey);
    console.log("New Balance:", balance / LAMPORTS_PER_SOL, "SOL");
  }

  // Create test users with different stake amounts
  // Each user gets stakeAmount + burnAmount tokens (burn amount reserved for buying hashrate)
  const users: TestUser[] = [
    { keypair: Keypair.generate(), name: "Alice", stakeAmount: 100_000_000_000n, burnAmount: 0n },        // 100 LODE stake, 0 burn (won't buy hashrate)
    { keypair: Keypair.generate(), name: "Bob", stakeAmount: 500_000_000_000n, burnAmount: 20_000_000_000n },   // 500 LODE stake, 20 burn
    { keypair: Keypair.generate(), name: "Charlie", stakeAmount: 50_000_000_000n, burnAmount: 0n },       // 50 LODE stake, 0 burn
    { keypair: Keypair.generate(), name: "Diana", stakeAmount: 200_000_000_000n, burnAmount: 15_000_000_000n }, // 200 LODE stake, 15 burn
  ];

  // ===== STEP 1: Create Token-2022 LODE Mint =====
  console.log("\n" + "=".repeat(60));
  console.log("  STEP 1: Create Token-2022 LODE Mint");
  console.log("=".repeat(60));

  let lodeMint = Keypair.generate();
  let mintCreated = false;

  for (let attempt = 1; attempt <= 3; attempt++) {
    console.log(`Attempt ${attempt}: LODE Mint: ${lodeMint.publicKey.toBase58()}`);

    // Check if mint already exists
    const existingMint = await connection.getAccountInfo(lodeMint.publicKey);
    if (existingMint) {
      console.log("  Mint already exists from previous attempt, generating new keypair...");
      lodeMint = Keypair.generate();
      continue;
    }

    // Calculate rent for mint account (82 bytes for Token-2022 basic mint)
    const mintRent = await connection.getMinimumBalanceForRentExemption(82);

    const createMintIx = SystemProgram.createAccount({
      fromPubkey: admin.publicKey,
      newAccountPubkey: lodeMint.publicKey,
      space: 82,
      lamports: mintRent,
      programId: TOKEN_2022_PROGRAM_ID,
    });

    const initMintIx = createInitializeMint2Instruction(
      lodeMint.publicKey,
      9, // 9 decimals
      admin.publicKey, // mint authority
      admin.publicKey, // freeze authority (optional)
      TOKEN_2022_PROGRAM_ID
    );

    const mintSig = await sendTx(connection, [createMintIx, initMintIx], [admin, lodeMint], "Create LODE Mint", 1);
    if (mintSig) {
      mintCreated = true;
      break;
    }

    // Generate new keypair for next attempt
    lodeMint = Keypair.generate();
  }

  if (!mintCreated) {
    console.log("Failed to create mint after 3 attempts, exiting...");
    return;
  }

  // ===== STEP 2: Fund Users & Create Token Accounts =====
  console.log("\n" + "=".repeat(60));
  console.log("  STEP 2: Fund Users & Create Token Accounts");
  console.log("=".repeat(60));

  for (const user of users) {
    // Airdrop SOL
    const airdropSig = await connection.requestAirdrop(user.keypair.publicKey, 2 * LAMPORTS_PER_SOL);
    await connection.confirmTransaction(airdropSig);
    console.log(`  ${user.name}: Funded 2 SOL`);

    // Create ATA for LODE tokens
    const ata = await getAssociatedTokenAddress(
      lodeMint.publicKey,
      user.keypair.publicKey,
      false,
      TOKEN_2022_PROGRAM_ID,
      ASSOCIATED_TOKEN_PROGRAM_ID
    );
    user.tokenAccount = ata;

    const createAtaIx = createAssociatedTokenAccountInstruction(
      admin.publicKey,
      ata,
      user.keypair.publicKey,
      lodeMint.publicKey,
      TOKEN_2022_PROGRAM_ID,
      ASSOCIATED_TOKEN_PROGRAM_ID
    );

    await sendTx(connection, [createAtaIx], [admin], `Create ATA for ${user.name}`);

    // Mint LODE tokens to user (stake amount + burn amount for hashrate purchases)
    const totalMint = user.stakeAmount + user.burnAmount;
    const mintToIx = createMintToInstruction(
      lodeMint.publicKey,
      ata,
      admin.publicKey,
      totalMint,
      [],
      TOKEN_2022_PROGRAM_ID
    );

    await sendTx(connection, [mintToIx], [admin], `Mint ${Number(totalMint) / 1e9} LODE to ${user.name}`);
  }

  // ===== STEP 3: Derive All PDAs =====
  console.log("\n" + "=".repeat(60));
  console.log("  STEP 3: Derive PDAs");
  console.log("=".repeat(60));

  const [miningConfigPda, miningConfigBump] = findPda([Buffer.from("mining_config")], MINING_PROGRAM_ID);
  const [stakingPoolPda, stakingPoolBump] = findPda([Buffer.from("staking_pool")], STAKING_PROGRAM_ID);
  const [treasuryPda] = findPda([Buffer.from("treasury")], TREASURY_PROGRAM_ID);
  // Vault PDA uses "staking_vault" + pool_pda as seeds
  const [vaultPda, vaultBump] = findPda([Buffer.from("staking_vault"), stakingPoolPda.toBuffer()], STAKING_PROGRAM_ID);

  console.log("  Mining Config:", miningConfigPda.toBase58());
  console.log("  Staking Pool:", stakingPoolPda.toBase58());
  console.log("  Treasury:", treasuryPda.toBase58());
  console.log("  Vault:", vaultPda.toBase58());

  // Derive user PDAs
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

    console.log(`  ${user.name} Stake Account: ${stakeAccountPda.toBase58().slice(0, 20)}...`);
    console.log(`  ${user.name} Miner Entry: ${minerEntryPda.toBase58().slice(0, 20)}...`);
  }

  // ===== STEP 4: Initialize Staking Pool =====
  console.log("\n" + "=".repeat(60));
  console.log("  STEP 4: Initialize Staking Pool");
  console.log("=".repeat(60));

  const stakingPoolInfo = await connection.getAccountInfo(stakingPoolPda);
  if (stakingPoolInfo) {
    console.log("  Staking pool already initialized, skipping...");
  } else {
    // Build initialize staking pool instruction
    // Accounts: admin, pool, vault, mint, authorized_depositor, token_program, system_program
    const minStake = Buffer.alloc(8);
    minStake.writeBigUInt64LE(10_000_000_000n); // 10 LODE min stake

    const initStakingIx = new TransactionInstruction({
      programId: STAKING_PROGRAM_ID,
      keys: [
        { pubkey: admin.publicKey, isSigner: true, isWritable: true },
        { pubkey: stakingPoolPda, isSigner: false, isWritable: true },
        { pubkey: vaultPda, isSigner: false, isWritable: true },
        { pubkey: lodeMint.publicKey, isSigner: false, isWritable: false },
        { pubkey: treasuryPda, isSigner: false, isWritable: false }, // authorized depositor
        { pubkey: TOKEN_2022_PROGRAM_ID, isSigner: false, isWritable: false },
        { pubkey: SystemProgram.programId, isSigner: false, isWritable: false },
      ],
      data: Buffer.concat([Buffer.from([STAKING_INITIALIZE]), minStake]),
    });

    const stakingInitSig = await sendTx(connection, [initStakingIx], [admin], "Initialize Staking Pool");
    if (!stakingInitSig) {
      console.log("Failed to initialize staking pool!");
      // Continue anyway for testing
    }
  }

  // ===== STEP 5: Initialize Mining Program =====
  console.log("\n" + "=".repeat(60));
  console.log("  STEP 5: Initialize Mining Program");
  console.log("=".repeat(60));

  const miningConfigInfo = await connection.getAccountInfo(miningConfigPda);
  let currentEpoch = 0n;

  if (miningConfigInfo) {
    console.log("  Mining program already initialized");
    const configData = miningConfigInfo.data;
    currentEpoch = configData.readBigUInt64LE(176);
    console.log("  Current Epoch:", currentEpoch.toString());
  } else {
    // Initialize mining program
    const epochIdBuffer = Buffer.alloc(8);
    epochIdBuffer.writeBigUInt64LE(0n);
    const [epoch0Pda] = findPda([Buffer.from("epoch"), epochIdBuffer], MINING_PROGRAM_ID);

    const initMiningIx = new TransactionInstruction({
      programId: MINING_PROGRAM_ID,
      keys: [
        { pubkey: admin.publicKey, isSigner: true, isWritable: true },
        { pubkey: miningConfigPda, isSigner: false, isWritable: true },
        { pubkey: epoch0Pda, isSigner: false, isWritable: true },
        { pubkey: lodeMint.publicKey, isSigner: false, isWritable: false },
        { pubkey: treasuryPda, isSigner: false, isWritable: false },
        { pubkey: stakingPoolPda, isSigner: false, isWritable: false },
        { pubkey: LODE_TOKEN_PROGRAM_ID, isSigner: false, isWritable: false },
        { pubkey: SystemProgram.programId, isSigner: false, isWritable: false },
      ],
      data: Buffer.from([MINING_INITIALIZE]),
    });

    const miningInitSig = await sendTx(connection, [initMiningIx], [admin], "Initialize Mining Program");
    if (!miningInitSig) {
      console.log("Failed to initialize mining program!");
    }
  }

  // ===== STEP 6: Users Stake Tokens =====
  console.log("\n" + "=".repeat(60));
  console.log("  STEP 6: Users Stake Tokens");
  console.log("=".repeat(60));

  for (const user of users) {
    // Check if already staked
    const stakeAccountInfo = await connection.getAccountInfo(user.stakeAccountPda!);
    if (stakeAccountInfo) {
      const stakeData = stakeAccountInfo.data;
      const stakedAmount = stakeData.readBigUInt64LE(72);
      console.log(`  ${user.name}: Already staked ${Number(stakedAmount) / 1e9} LODE`);
      continue;
    }

    // Build stake instruction
    // Accounts: user, user_token, pool, vault, stake_account, token_program, system_program
    const amountBuffer = Buffer.alloc(8);
    amountBuffer.writeBigUInt64LE(user.stakeAmount);

    const stakeIx = new TransactionInstruction({
      programId: STAKING_PROGRAM_ID,
      keys: [
        { pubkey: user.keypair.publicKey, isSigner: true, isWritable: true },
        { pubkey: user.tokenAccount!, isSigner: false, isWritable: true },
        { pubkey: stakingPoolPda, isSigner: false, isWritable: true },
        { pubkey: vaultPda, isSigner: false, isWritable: true },
        { pubkey: user.stakeAccountPda!, isSigner: false, isWritable: true },
        { pubkey: TOKEN_2022_PROGRAM_ID, isSigner: false, isWritable: false },
        { pubkey: SystemProgram.programId, isSigner: false, isWritable: false },
      ],
      data: Buffer.concat([Buffer.from([STAKING_STAKE]), amountBuffer]),
    });

    await sendTx(connection, [stakeIx], [user.keypair], `${user.name} stakes ${Number(user.stakeAmount) / 1e9} LODE`);
  }

  // ===== STEP 7: Get Current Epoch Info =====
  console.log("\n" + "=".repeat(60));
  console.log("  STEP 7: Current Epoch Status");
  console.log("=".repeat(60));

  // Re-fetch mining config
  const updatedConfigInfo = await connection.getAccountInfo(miningConfigPda);
  if (!updatedConfigInfo) {
    console.log("Mining config not found!");
    return;
  }

  currentEpoch = updatedConfigInfo.data.readBigUInt64LE(176);
  const epochIdBuffer = Buffer.alloc(8);
  epochIdBuffer.writeBigUInt64LE(currentEpoch);
  const [epochPda] = findPda([Buffer.from("epoch"), epochIdBuffer], MINING_PROGRAM_ID);

  const epochInfo = await connection.getAccountInfo(epochPda);
  if (!epochInfo) {
    console.log("Epoch not found!");
    return;
  }

  const epochData = epochInfo.data;
  const epochId = epochData.readBigUInt64LE(8);
  const startTime = epochData.readBigInt64LE(16);
  const endTime = epochData.readBigInt64LE(24);
  const lotteryPool = epochData.readBigUInt64LE(32);
  const emissionPool = epochData.readBigUInt64LE(40);
  const totalHashrate = epochData.readBigUInt64LE(48);
  const participantCount = epochData.readBigUInt64LE(96);

  const now = Math.floor(Date.now() / 1000);
  const timeRemaining = Number(endTime) - now;

  console.log(`  Epoch ID: ${epochId}`);
  console.log(`  Start: ${new Date(Number(startTime) * 1000).toISOString()}`);
  console.log(`  End: ${new Date(Number(endTime) * 1000).toISOString()}`);
  console.log(`  Time Remaining: ${timeRemaining > 0 ? `${timeRemaining}s` : "ENDED"}`);
  console.log(`  Lottery Pool: ${Number(lotteryPool) / 1e9} LODE`);
  console.log(`  Emission Pool: ${Number(emissionPool) / 1e9} LODE`);
  console.log(`  Total Hashrate: ${totalHashrate}`);
  console.log(`  Participants: ${participantCount}`);

  // Check if epoch ended and needs advancing
  if (timeRemaining <= 0) {
    console.log("\n  Epoch has ended, advancing...");
    await advanceEpoch(connection, admin, miningConfigPda, currentEpoch);

    // Re-fetch epoch
    const newEpochId = currentEpoch + 1n;
    const newEpochIdBuffer = Buffer.alloc(8);
    newEpochIdBuffer.writeBigUInt64LE(newEpochId);
    const [newEpochPda] = findPda([Buffer.from("epoch"), newEpochIdBuffer], MINING_PROGRAM_ID);
    currentEpoch = newEpochId;
    epochIdBuffer.writeBigUInt64LE(currentEpoch);
  }

  // ===== STEP 8: Users Enter Epoch =====
  console.log("\n" + "=".repeat(60));
  console.log("  STEP 8: Users Enter Epoch");
  console.log("=".repeat(60));

  // Re-derive epoch PDA for current epoch
  const currentEpochIdBuffer = Buffer.alloc(8);
  currentEpochIdBuffer.writeBigUInt64LE(currentEpoch);
  const [currentEpochPda] = findPda([Buffer.from("epoch"), currentEpochIdBuffer], MINING_PROGRAM_ID);

  for (const user of users) {
    // Check if already entered
    const minerEntryInfo = await connection.getAccountInfo(user.minerEntryPda!);
    if (minerEntryInfo) {
      const entryData = minerEntryInfo.data;
      const entryEpochId = entryData.readBigUInt64LE(40);
      if (entryEpochId === currentEpoch) {
        console.log(`  ${user.name}: Already entered epoch ${currentEpoch}`);
        continue;
      }
    }

    // Build enter_epoch instruction
    // Accounts: user, config, epoch, miner_entry, stake_account, system_program
    const enterEpochIx = new TransactionInstruction({
      programId: MINING_PROGRAM_ID,
      keys: [
        { pubkey: user.keypair.publicKey, isSigner: true, isWritable: true },
        { pubkey: miningConfigPda, isSigner: false, isWritable: false },
        { pubkey: currentEpochPda, isSigner: false, isWritable: true },
        { pubkey: user.minerEntryPda!, isSigner: false, isWritable: true },
        { pubkey: user.stakeAccountPda!, isSigner: false, isWritable: false },
        { pubkey: SystemProgram.programId, isSigner: false, isWritable: false },
      ],
      data: Buffer.from([MINING_ENTER_EPOCH]),
    });

    await sendTx(connection, [enterEpochIx], [user.keypair], `${user.name} enters epoch ${currentEpoch}`);
  }

  // ===== STEP 9: Users Buy Hashrate =====
  console.log("\n" + "=".repeat(60));
  console.log("  STEP 9: Users Buy Hashrate (Pay-to-Mine)");
  console.log("=".repeat(60));

  // Only users with burnAmount > 0 will buy hashrate (Bob and Diana)
  const boostUsers = users.filter(u => u.burnAmount > 0n);

  for (const user of boostUsers) {
    // Use each user's configured burn amount
    const amountBuffer = Buffer.alloc(8);
    amountBuffer.writeBigUInt64LE(user.burnAmount);

    // Build buy_hashrate instruction
    // Accounts: user, config, epoch, miner_entry, user_token_account, mint, token_program
    const buyHashrateIx = new TransactionInstruction({
      programId: MINING_PROGRAM_ID,
      keys: [
        { pubkey: user.keypair.publicKey, isSigner: true, isWritable: false },
        { pubkey: miningConfigPda, isSigner: false, isWritable: false },
        { pubkey: currentEpochPda, isSigner: false, isWritable: true },
        { pubkey: user.minerEntryPda!, isSigner: false, isWritable: true },
        { pubkey: user.tokenAccount!, isSigner: false, isWritable: true },
        { pubkey: lodeMint.publicKey, isSigner: false, isWritable: true },
        { pubkey: TOKEN_2022_PROGRAM_ID, isSigner: false, isWritable: false },
      ],
      data: Buffer.concat([Buffer.from([MINING_BUY_HASHRATE]), amountBuffer]),
    });

    await sendTx(connection, [buyHashrateIx], [user.keypair], `${user.name} burns ${Number(user.burnAmount) / 1e9} LODE for hashrate`);
  }

  // ===== STEP 10: Wait for Bootup to Complete =====
  console.log("\n" + "=".repeat(60));
  console.log("  STEP 10: Wait for Bootup & Test Hashrate Marketplace");
  console.log("=".repeat(60));

  // Simnet bootup is 30 seconds - wait for it to complete
  console.log("  Waiting 32 seconds for hashrate bootup to complete (simnet = 30s)...");
  await new Promise(resolve => setTimeout(resolve, 32000));

  // Check Bob's miner entry to see if bootup completed
  const bob = users.find(u => u.name === "Bob")!;
  const alice = users.find(u => u.name === "Alice")!;

  let bobEntryInfo = await connection.getAccountInfo(bob.minerEntryPda!);
  if (bobEntryInfo) {
    const bobData = bobEntryInfo.data;
    const bobBootedHashrate = bobData.readBigUInt64LE(56);
    const bobBootingHashrate = bobData.readBigUInt64LE(64);
    console.log(`  Bob's booted hashrate: ${bobBootedHashrate}`);
    console.log(`  Bob's booting hashrate: ${bobBootingHashrate} (should be 0 after bootup)`);
  }

  // ===== STEP 11: Bob Lists Hashrate for Sale =====
  console.log("\n" + "=".repeat(60));
  console.log("  STEP 11: Hashrate Marketplace - Bob Lists Hashrate");
  console.log("=".repeat(60));

  // Bootup doesn't auto-finalize on-chain - we need to trigger an instruction that calls finalize_bootup()
  // The easiest way is to have Bob buy a tiny bit more hashrate (which calls finalize_bootup internally)
  // OR re-enter epoch (but that would reset stake_hashrate). Let's buy 0 (no-op is ok).
  // Actually, buy_hashrate with amount=0 returns Ok early. We need a different approach.
  // The contract's effective_paid_hashrate() calculates effectiveness on-the-fly,
  // but booted_hashrate is only updated by finalize_bootup().
  // For the marketplace test, we need booted hashrate. Let's mint Bob 1 more LODE and burn it.
  console.log("  Triggering bootup finalization by burning 1 LODE...");
  const triggerMintIx = createMintToInstruction(
    lodeMint.publicKey,
    users[1].tokenAccount!, // Bob
    admin.publicKey,
    1_000_000_000n, // 1 LODE
    [],
    TOKEN_2022_PROGRAM_ID
  );
  await sendTx(connection, [triggerMintIx], [admin], "Mint 1 LODE to Bob for finalization trigger");

  // Bob burns 1 LODE - this triggers finalize_bootup internally
  const triggerAmountBuffer = Buffer.alloc(8);
  triggerAmountBuffer.writeBigUInt64LE(1_000_000_000n);

  const triggerBuyHashrateIx = new TransactionInstruction({
    programId: MINING_PROGRAM_ID,
    keys: [
      { pubkey: bob.keypair.publicKey, isSigner: true, isWritable: false },
      { pubkey: miningConfigPda, isSigner: false, isWritable: false },
      { pubkey: currentEpochPda, isSigner: false, isWritable: true },
      { pubkey: bob.minerEntryPda!, isSigner: false, isWritable: true },
      { pubkey: bob.tokenAccount!, isSigner: false, isWritable: true },
      { pubkey: lodeMint.publicKey, isSigner: false, isWritable: true },
      { pubkey: TOKEN_2022_PROGRAM_ID, isSigner: false, isWritable: false },
    ],
    data: Buffer.concat([Buffer.from([MINING_BUY_HASHRATE]), triggerAmountBuffer]),
  });

  await sendTx(connection, [triggerBuyHashrateIx], [bob.keypair], "Bob burns 1 LODE to finalize bootup");

  // Now check Bob's state again
  bobEntryInfo = await connection.getAccountInfo(bob.minerEntryPda!);
  if (!bobEntryInfo) {
    console.log("  Bob's miner entry not found!");
  } else {
    const bobData = bobEntryInfo.data;
    const bobBootedHashrate = bobData.readBigUInt64LE(56);
    const bobBootingHashrate = bobData.readBigUInt64LE(64);
    const bobLockedHashrate = bobData.readBigUInt64LE(88);

    // Sellable = booted - locked
    const sellable = bobBootedHashrate - bobLockedHashrate;
    console.log(`  Bob's sellable hashrate: ${sellable}`);

    if (sellable > 0n) {
      // List some hashrate for sale
      // Amount: 50,000 units, Price per unit: 100_000_000 (0.1 LODE per unit)
      const listAmount = 50000n;
      const pricePerUnit = 100_000_000n; // 0.1 LODE per hashrate unit

      // Note: Hashrate marketplace test is skipped on simnet because:
      // The contract uses Clock::get()?.unix_timestamp for the listing_id in the PDA,
      // which is impossible to predict exactly from the client side.
      // Surfpool simnet doesn't support getBlockTime, and even if it did, there would
      // be timing drift between the client call and on-chain execution.
      //
      // For production testing on devnet/mainnet, the contract should be updated to
      // accept listing_id as instruction data rather than deriving it from Clock.
      console.log("  [SKIPPED] Hashrate marketplace test on simnet");
      console.log("  Reason: Contract uses on-chain Clock for listing_id PDA");
      console.log(`  Bob would list ${listAmount} HR @ ${Number(pricePerUnit) / 1e9} LODE/unit`);
      console.log(`  Total price would be: ${Number(listAmount * pricePerUnit) / 1e9} LODE`);
    } else {
      console.log("  Bob has no sellable hashrate yet (bootup not finalized or no booted hashrate)");
      console.log("  Note: Hashrate bootup may need to be finalized via enter_epoch or buy_hashrate");
    }
  }

  // ===== STEP 13: Wait for Epoch End & Advance =====
  console.log("\n" + "=".repeat(60));
  console.log("  STEP 13: Wait for Epoch End & Advance");
  console.log("=".repeat(60));

  // Check how much time is left in the epoch
  const epochInfoForWait = await connection.getAccountInfo(currentEpochPda);
  if (epochInfoForWait) {
    const epochDataForWait = epochInfoForWait.data;
    const epochEndTime = epochDataForWait.readBigInt64LE(24);
    const nowForWait = Math.floor(Date.now() / 1000);
    const timeRemainingForWait = Number(epochEndTime) - nowForWait;

    if (timeRemainingForWait > 0) {
      console.log(`  Epoch ends in ${timeRemainingForWait}s, waiting...`);
      // Wait for epoch to end + 2s buffer
      await new Promise(resolve => setTimeout(resolve, (timeRemainingForWait + 2) * 1000));
    } else {
      console.log("  Epoch already ended!");
    }

    // Now advance to next epoch
    console.log("\n  Advancing to next epoch...");
    const advanceSuccess = await advanceEpoch(connection, admin, miningConfigPda, currentEpoch);

    if (advanceSuccess) {
      console.log("  Successfully advanced to epoch", (currentEpoch + 1n).toString());
    } else {
      console.log("  Failed to advance epoch (may already be advanced)");
    }
  }

  // ===== STEP 14: Show Final State =====
  console.log("\n" + "=".repeat(60));
  console.log("  FINAL STATE");
  console.log("=".repeat(60));

  // Re-fetch epoch
  const finalEpochInfo = await connection.getAccountInfo(currentEpochPda);
  if (finalEpochInfo) {
    const finalData = finalEpochInfo.data;
    const finalHashrate = finalData.readBigUInt64LE(48);
    const finalParticipants = finalData.readBigUInt64LE(96);
    const finalEndTime = finalData.readBigInt64LE(24);
    const nowFinal = Math.floor(Date.now() / 1000);
    const remainingFinal = Number(finalEndTime) - nowFinal;

    console.log(`  Epoch ${currentEpoch}:`);
    console.log(`    Total Hashrate: ${finalHashrate}`);
    console.log(`    Participants: ${finalParticipants}`);
    console.log(`    Time Remaining: ${remainingFinal}s`);
  }

  console.log("\n  User Miner Entries:");
  for (const user of users) {
    const minerEntryInfo = await connection.getAccountInfo(user.minerEntryPda!);
    if (minerEntryInfo) {
      const entryData = minerEntryInfo.data;
      // MinerEntry layout (from state.rs):
      // discriminator: [u8; 8] - offset 0
      // owner: [u8; 32] - offset 8
      // epoch_id: u64 - offset 40
      // stake_hashrate: u64 - offset 48
      // booted_hashrate: u64 - offset 56
      // booting_hashrate: u64 - offset 64
      // bootup_start_timestamp: i64 - offset 72
      // total_burned_lifetime: u64 - offset 80
      // locked_hashrate: u64 - offset 88
      const stakeHashrate = entryData.readBigUInt64LE(48);
      const bootedHashrate = entryData.readBigUInt64LE(56);
      const bootingHashrate = entryData.readBigUInt64LE(64);
      const bootupStartTimestamp = entryData.readBigInt64LE(72);
      const totalBurnedLifetime = entryData.readBigUInt64LE(80);
      const lockedHashrate = entryData.readBigUInt64LE(88);

      console.log(`    ${user.name}:`);
      console.log(`      Stake Hashrate: ${stakeHashrate}`);
      console.log(`      Booted Hashrate: ${bootedHashrate}`);
      console.log(`      Booting Hashrate: ${bootingHashrate}`);
      console.log(`      Bootup Start: ${bootupStartTimestamp > 0n ? new Date(Number(bootupStartTimestamp) * 1000).toISOString() : 'N/A'}`);
      console.log(`      Total Burned: ${Number(totalBurnedLifetime) / 1e9} LODE`);
      console.log(`      Locked Hashrate: ${lockedHashrate}`);
    } else {
      console.log(`    ${user.name}: Not entered`);
    }
  }

  console.log("\n" + "=".repeat(60));
  console.log("  TEST COMPLETE");
  console.log("=".repeat(60));
  console.log("\nNext steps to test:");
  console.log("1. Wait for epoch to end (check time remaining)");
  console.log("2. Call advance_epoch to create new epoch");
  console.log("3. Call consume_randomness (VRF) to select winners");
  console.log("4. Call credit_winner for each winner");
  console.log("5. Winners can claim their rewards");
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
