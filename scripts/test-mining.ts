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
const TOKEN_PROGRAM_ID = new PublicKey("7d1TQ2HKfzQELVhctnhxwMT6peGrYdXh7jWcpxJTxjr1");
const TOKEN_2022_ID = new PublicKey("TokenzQdBNbLqP5VEhdkAS6EPFLC1PHnBqCXEpPxuEb");

// Instruction discriminators
const INITIALIZE = 0;
const ADVANCE_EPOCH = 1;
const ENTER_EPOCH = 2;

function findPda(seeds: Buffer[], programId: PublicKey): [PublicKey, number] {
  return PublicKey.findProgramAddressSync(seeds, programId);
}

async function loadKeypair(path: string): Promise<Keypair> {
  const data = JSON.parse(fs.readFileSync(path, "utf-8"));
  return Keypair.fromSecretKey(Uint8Array.from(data));
}

async function main() {
  const connection = new Connection("http://127.0.0.1:8899", "confirmed");

  // Try to load payer from default solana CLI config path or use a new keypair
  let payer: Keypair;
  const configPath = `${process.env.HOME}/.config/solana/id.json`;

  if (fs.existsSync(configPath)) {
    payer = await loadKeypair(configPath);
    console.log("Loaded keypair from:", configPath);
  } else {
    payer = Keypair.generate();
    console.log("Generated new keypair");
  }

  // Request airdrop if needed
  const balance = await connection.getBalance(payer.publicKey);
  console.log("Payer:", payer.publicKey.toBase58());
  console.log("Balance:", balance / LAMPORTS_PER_SOL, "SOL");

  if (balance < LAMPORTS_PER_SOL) {
    console.log("Requesting airdrop...");
    const sig = await connection.requestAirdrop(payer.publicKey, 10 * LAMPORTS_PER_SOL);
    await connection.confirmTransaction(sig);
    console.log("Airdrop confirmed!");
  }

  console.log("\n=== LODE Mining Test Script ===\n");

  // Derive all PDAs
  const [configPda] = findPda([Buffer.from("mining_config")], MINING_PROGRAM_ID);
  const [stakingPoolPda] = findPda([Buffer.from("staking_pool")], STAKING_PROGRAM_ID);
  const [treasuryPda] = findPda([Buffer.from("treasury")], TREASURY_PROGRAM_ID);

  console.log("Derived PDAs:");
  console.log("  Mining Config:", configPda.toBase58());
  console.log("  Staking Pool:", stakingPoolPda.toBase58());
  console.log("  Treasury:", treasuryPda.toBase58());

  // Check if config exists
  const configInfo = await connection.getAccountInfo(configPda);

  if (configInfo) {
    const { currentEpoch, hasEnded } = await displayConfig(connection, configPda, configInfo);

    // If epoch has ended, try to advance it
    if (hasEnded) {
      const advanced = await advanceEpoch(connection, payer, configPda, currentEpoch);
      if (advanced) {
        // Re-fetch and display updated state
        const newConfigInfo = await connection.getAccountInfo(configPda);
        if (newConfigInfo) {
          await displayConfig(connection, configPda, newConfigInfo);
        }
      }
    }
  } else {
    console.log("\nConfig not initialized yet!");
    console.log("\n=== Initializing Mining Program ===");

    // For testing, we'll create a mock mint
    const mint = Keypair.generate();

    // Epoch 0 PDA
    const epochIdBuffer = Buffer.alloc(8);
    epochIdBuffer.writeBigUInt64LE(0n);
    const [epoch0Pda] = findPda([Buffer.from("epoch"), epochIdBuffer], MINING_PROGRAM_ID);

    console.log("Epoch 0 PDA:", epoch0Pda.toBase58());
    console.log("Mock Mint:", mint.publicKey.toBase58());

    // Build Initialize instruction
    // Accounts:
    // 0. Admin (signer, writable)
    // 1. Mining config PDA (writable)
    // 2. Epoch 0 PDA (writable)
    // 3. LODE mint
    // 4. Treasury program
    // 5. Staking pool
    // 6. LODE token program
    // 7. System program

    const initIx = new TransactionInstruction({
      programId: MINING_PROGRAM_ID,
      keys: [
        { pubkey: payer.publicKey, isSigner: true, isWritable: true },
        { pubkey: configPda, isSigner: false, isWritable: true },
        { pubkey: epoch0Pda, isSigner: false, isWritable: true },
        { pubkey: mint.publicKey, isSigner: false, isWritable: false },  // Mock mint for now
        { pubkey: treasuryPda, isSigner: false, isWritable: false },
        { pubkey: stakingPoolPda, isSigner: false, isWritable: false },
        { pubkey: TOKEN_PROGRAM_ID, isSigner: false, isWritable: false },  // Our lode-token program
        { pubkey: SystemProgram.programId, isSigner: false, isWritable: false },
      ],
      data: Buffer.from([INITIALIZE]),
    });

    try {
      const tx = new Transaction().add(initIx);
      // Get a fresh blockhash
      const { blockhash, lastValidBlockHeight } = await connection.getLatestBlockhash("finalized");
      tx.recentBlockhash = blockhash;
      tx.feePayer = payer.publicKey;

      const sig = await sendAndConfirmTransaction(connection, tx, [payer], {
        commitment: "confirmed",
        maxRetries: 5,
      });
      console.log("\nInitialize transaction confirmed:", sig);

      // Re-fetch and display config
      const newConfigInfo = await connection.getAccountInfo(configPda);
      if (newConfigInfo) {
        await displayConfig(connection, configPda, newConfigInfo);
      }
    } catch (e: any) {
      console.error("\nInitialize failed:", e.message);
      if (e.logs) {
        console.error("Logs:", e.logs.slice(-10).join("\n"));
      }
    }
  }
}

async function advanceEpoch(connection: Connection, payer: Keypair, configPda: PublicKey, currentEpochId: bigint) {
  console.log("\n=== Advancing Epoch ===");

  // Current epoch PDA
  const currentEpochIdBuffer = Buffer.alloc(8);
  currentEpochIdBuffer.writeBigUInt64LE(currentEpochId);
  const [currentEpochPda] = findPda([Buffer.from("epoch"), currentEpochIdBuffer], MINING_PROGRAM_ID);

  // Next epoch PDA
  const nextEpochId = currentEpochId + 1n;
  const nextEpochIdBuffer = Buffer.alloc(8);
  nextEpochIdBuffer.writeBigUInt64LE(nextEpochId);
  const [nextEpochPda] = findPda([Buffer.from("epoch"), nextEpochIdBuffer], MINING_PROGRAM_ID);

  console.log("Current Epoch PDA:", currentEpochPda.toBase58());
  console.log("Next Epoch PDA:", nextEpochPda.toBase58());

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
    console.log("\nAdvance Epoch transaction confirmed:", sig);
    return true;
  } catch (e: any) {
    console.error("\nAdvance Epoch failed:", e.message);
    if (e.logs) {
      console.error("Logs:", e.logs.slice(-10).join("\n"));
    }
    return false;
  }
}

async function displayConfig(connection: Connection, configPda: PublicKey, configInfo: any): Promise<{ currentEpoch: bigint; hasEnded: boolean }> {
  console.log("\n=== Mining Config ===");
  console.log("Size:", configInfo.data.length);
  console.log("Owner:", configInfo.owner.toBase58());

  // Parse MiningConfig
  // Layout based on state.rs:
  // discriminator: [u8; 8]      → 0-8
  // mint: [u8; 32]              → 8-40
  // admin: [u8; 32]             → 40-72
  // treasury: [u8; 32]          → 72-104
  // staking_pool: [u8; 32]      → 104-136
  // lode_token_program: [u8; 32] → 136-168
  // genesis_timestamp: i64      → 168-176
  // current_epoch: u64          → 176-184
  // total_emitted: u64          → 184-192
  // bump: u8                    → 192
  // initialized: u8             → 193
  // _padding: [u8; 6]           → 194-200
  // TOTAL = 200

  const data = configInfo.data;
  const discriminator = data.readBigUInt64LE(0);
  const mint = new PublicKey(data.slice(8, 40));
  const admin = new PublicKey(data.slice(40, 72));
  const treasury = new PublicKey(data.slice(72, 104));
  const stakingPool = new PublicKey(data.slice(104, 136));
  const lodeTokenProgram = new PublicKey(data.slice(136, 168));
  const genesisTimestamp = data.readBigInt64LE(168);
  const currentEpoch = data.readBigUInt64LE(176);
  const totalEmitted = data.readBigUInt64LE(184);
  const bump = data[192];
  const initialized = data[193];

  console.log("\nParsed Config:");
  console.log("  Discriminator:", discriminator.toString());
  console.log("  Mint:", mint.toBase58());
  console.log("  Admin:", admin.toBase58());
  console.log("  Genesis:", new Date(Number(genesisTimestamp) * 1000).toISOString());
  console.log("  Current Epoch:", currentEpoch.toString());
  console.log("  Total Emitted:", totalEmitted.toString());
  console.log("  Bump:", bump);
  console.log("  Initialized:", initialized === 1 ? "Yes" : "No");

  // Get current epoch PDA
  const epochId = Number(currentEpoch);
  const epochIdBuffer = Buffer.alloc(8);
  epochIdBuffer.writeBigUInt64LE(BigInt(epochId));
  const [epochPda] = findPda([Buffer.from("epoch"), epochIdBuffer], MINING_PROGRAM_ID);

  console.log("\n=== Current Epoch ===");
  console.log("Epoch PDA:", epochPda.toBase58());

  const epochInfo = await connection.getAccountInfo(epochPda);
  if (epochInfo) {
    // Parse Epoch based on state.rs:
    // discriminator: [u8; 8]      → 0-8
    // id: u64                      → 8-16
    // start_time: i64              → 16-24
    // end_time: i64                → 24-32
    // lottery_pool: u64            → 32-40
    // emission_pool: u64           → 40-48
    // total_hashrate_lo: u64       → 48-56
    // total_hashrate_hi: u64       → 56-64
    // vrf_seed: [u8; 32]           → 64-96
    // participant_count: u64       → 96-104
    // vrf_fulfilled: u8            → 104
    // winners_drawn: u8            → 105
    // bump: u8                     → 106
    // _padding: [u8; 5]            → 107-112
    // winners: [[u8; 32]; 64]      → 112+

    const epochData = epochInfo.data;
    const id = epochData.readBigUInt64LE(8);
    const startTime = epochData.readBigInt64LE(16);
    const endTime = epochData.readBigInt64LE(24);
    const lotteryPool = epochData.readBigUInt64LE(32);
    const emissionPool = epochData.readBigUInt64LE(40);
    // total_hashrate is u128 stored as lo/hi
    const totalHashrateLow = epochData.readBigUInt64LE(48);
    const totalHashrateHigh = epochData.readBigUInt64LE(56);
    const participantCount = epochData.readBigUInt64LE(96);
    const vrfFulfilled = epochData[104];
    const winnersDrawn = epochData[105];

    const now = Math.floor(Date.now() / 1000);
    const timeRemaining = Number(endTime) - now;

    console.log("Size:", epochInfo.data.length);
    console.log("\nParsed Epoch:");
    console.log("  ID:", id.toString());
    console.log("  Start:", new Date(Number(startTime) * 1000).toISOString());
    console.log("  End:", new Date(Number(endTime) * 1000).toISOString());
    console.log("  Time Remaining:", timeRemaining > 0 ? `${timeRemaining} seconds (${(timeRemaining / 3600).toFixed(1)} hours)` : "ENDED");
    console.log("  Lottery Pool:", lotteryPool.toString());
    console.log("  Emission Pool:", (Number(emissionPool) / 1e9).toFixed(2), "LODE");
    console.log("  Total Hashrate:", totalHashrateLow.toString());
    console.log("  Participants:", participantCount.toString());
    console.log("  VRF Fulfilled:", vrfFulfilled === 1 ? "Yes" : "No");
    console.log("  Winners Drawn:", winnersDrawn);

    if (timeRemaining <= 0) {
      console.log("\n*** EPOCH HAS ENDED - Ready to advance! ***");
      return { currentEpoch, hasEnded: true };
    }
  } else {
    console.log("Epoch not found!");
  }

  return { currentEpoch, hasEnded: false };
}

main().catch(console.error);
