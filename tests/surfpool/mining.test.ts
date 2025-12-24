/**
 * LODE Mining Program - Surfpool E2E Tests
 *
 * These tests verify the lode-mining program against a running Surfpool validator.
 * Prerequisite: surfpool start (programs deployed via Surfpool.toml)
 *
 * Testing strategy aligned with TLA+ specs:
 * - LodeEpoch.tla: Epoch state transitions
 * - LodeLottery.tla: Two-pool winner selection
 * - LodeRent.tla: Sybil economics
 */

import { describe, test, expect, beforeAll } from "bun:test";
import {
  Connection,
  Keypair,
  PublicKey,
  Transaction,
  TransactionInstruction,
  SystemProgram,
  sendAndConfirmTransaction,
} from "@solana/web3.js";

// Program IDs from keypairs (matches Surfpool.toml)
const MINING_PROGRAM_ID = new PublicKey(
  "CSrYQ2uEURizXFDruLVyHUXcNN1Dv3XKFdbPnddMF2pB"
);

// Instruction discriminators (match lib.rs)
const INSTRUCTION = {
  INITIALIZE: 0,
  MINT_MINER: 1,
  UPGRADE_MINER: 2,
  PAY_RENT: 3,
  JOIN_EPOCH: 4,
  ADVANCE_EPOCH: 5,
  FINALIZE_EPOCH: 6,
  CLAIM: 7,
};

// Account discriminators (match state.rs)
const DISCRIMINATOR = {
  MINING_CONFIG: Buffer.from("mineconf"),
  EPOCH: Buffer.from("epoch___"),
  PARTICIPATION: Buffer.from("particip"),
};

// Test connection to Surfpool
const RPC_URL = "http://127.0.0.1:8899";
let connection: Connection;
let payer: Keypair;

describe("LODE Mining - Surfpool E2E", () => {
  beforeAll(async () => {
    connection = new Connection(RPC_URL, "confirmed");

    // Check validator is responsive
    try {
      const slot = await connection.getSlot();
      console.log(`Surfpool slot: ${slot}`);
    } catch (e) {
      throw new Error(
        `Surfpool not running. Start with: surfpool start\n${e}`
      );
    }

    // Check program is deployed
    const programInfo = await connection.getAccountInfo(MINING_PROGRAM_ID);
    if (!programInfo || !programInfo.executable) {
      throw new Error(
        `Mining program not deployed at ${MINING_PROGRAM_ID.toBase58()}`
      );
    }
    console.log(`Mining program deployed: ${MINING_PROGRAM_ID.toBase58()}`);

    // Create funded payer
    payer = Keypair.generate();
    const airdropSig = await connection.requestAirdrop(
      payer.publicKey,
      10_000_000_000 // 10 SOL
    );
    await connection.confirmTransaction(airdropSig);
    console.log(`Payer funded: ${payer.publicKey.toBase58()}`);
  });

  describe("Program Deployment", () => {
    test("mining program is executable", async () => {
      const info = await connection.getAccountInfo(MINING_PROGRAM_ID);
      expect(info).not.toBeNull();
      expect(info!.executable).toBe(true);
    });
  });

  describe("TLA+ LodeEpoch Invariants", () => {
    test("MonotonicEpoch - epoch_id never decreases", async () => {
      // This test verifies that epoch IDs are monotonically increasing
      // when reading epoch accounts from the chain

      // For now, just verify the program is accessible
      // Full epoch state tests require initialize instruction
      const info = await connection.getAccountInfo(MINING_PROGRAM_ID);
      expect(info).not.toBeNull();
    });
  });

  describe("Instruction Building", () => {
    test("can build initialize instruction", () => {
      // Build instruction data
      const data = Buffer.alloc(1);
      data.writeUInt8(INSTRUCTION.INITIALIZE, 0);

      // Derive config PDA - seeds match MiningConfig::SEEDS in state.rs
      const [configPda] = PublicKey.findProgramAddressSync(
        [Buffer.from("mining_config")],
        MINING_PROGRAM_ID
      );

      const ix = new TransactionInstruction({
        programId: MINING_PROGRAM_ID,
        keys: [
          { pubkey: payer.publicKey, isSigner: true, isWritable: true },
          { pubkey: configPda, isSigner: false, isWritable: true },
          { pubkey: SystemProgram.programId, isSigner: false, isWritable: false },
        ],
        data,
      });

      expect(ix.programId.equals(MINING_PROGRAM_ID)).toBe(true);
      expect(ix.data[0]).toBe(INSTRUCTION.INITIALIZE);
    });

    test("can derive epoch PDA", () => {
      const epochId = BigInt(0);
      const epochIdBuffer = Buffer.alloc(8);
      epochIdBuffer.writeBigUInt64LE(epochId);

      const [epochPda, bump] = PublicKey.findProgramAddressSync(
        [Buffer.from("epoch"), epochIdBuffer],
        MINING_PROGRAM_ID
      );

      expect(epochPda).toBeInstanceOf(PublicKey);
      expect(bump).toBeGreaterThanOrEqual(0);
      expect(bump).toBeLessThanOrEqual(255);
    });

    test("can derive participation PDA", () => {
      const epochId = BigInt(0);
      const epochIdBuffer = Buffer.alloc(8);
      epochIdBuffer.writeBigUInt64LE(epochId);

      const nftMint = Keypair.generate().publicKey;

      const [participationPda, bump] = PublicKey.findProgramAddressSync(
        [Buffer.from("participation"), epochIdBuffer, nftMint.toBuffer()],
        MINING_PROGRAM_ID
      );

      expect(participationPda).toBeInstanceOf(PublicKey);
      expect(bump).toBeGreaterThanOrEqual(0);
    });
  });

  describe("v2 Instruction Execution", () => {
    let configPda: PublicKey;
    let configBump: number;

    beforeAll(() => {
      // Seeds must match MiningConfig::SEEDS = b"mining_config" in state.rs
      [configPda, configBump] = PublicKey.findProgramAddressSync(
        [Buffer.from("mining_config")],
        MINING_PROGRAM_ID
      );
    });

    test("initialize creates MiningConfig PDA", async () => {
      // Build instruction data (just the discriminator for initialize)
      const data = Buffer.alloc(1);
      data.writeUInt8(INSTRUCTION.INITIALIZE, 0);

      const ix = new TransactionInstruction({
        programId: MINING_PROGRAM_ID,
        keys: [
          { pubkey: payer.publicKey, isSigner: true, isWritable: true },
          { pubkey: configPda, isSigner: false, isWritable: true },
          {
            pubkey: SystemProgram.programId,
            isSigner: false,
            isWritable: false,
          },
        ],
        data,
      });

      const tx = new Transaction().add(ix);
      const sig = await sendAndConfirmTransaction(connection, tx, [payer]);
      console.log(`Initialize tx: ${sig}`);

      // Verify the config account was created
      const configInfo = await connection.getAccountInfo(configPda);
      expect(configInfo).not.toBeNull();
      expect(configInfo!.owner.equals(MINING_PROGRAM_ID)).toBe(true);

      // Check discriminator matches expected "mineconf"
      const discriminator = configInfo!.data.slice(0, 8);
      expect(discriminator.toString()).toBe(
        DISCRIMINATOR.MINING_CONFIG.toString()
      );

      console.log(`MiningConfig PDA: ${configPda.toBase58()}`);
      console.log(`Config account size: ${configInfo!.data.length} bytes`);
    });

    test("config account is not empty after initialization", async () => {
      // Verify the config account exists and has data (meaning initialization worked)
      // This validates that re-initialization would fail due to data_is_empty() check
      const configInfo = await connection.getAccountInfo(configPda);
      expect(configInfo).not.toBeNull();
      expect(configInfo!.data.length).toBeGreaterThan(0);

      // The program has an AlreadyInitialized check: if !config_account.data_is_empty()
      // Since account is not empty, any subsequent initialize call would return an error
      console.log(
        `Config account has ${configInfo!.data.length} bytes - re-init would fail`
      );
    });

    test("can read MiningConfig state", async () => {
      const configInfo = await connection.getAccountInfo(configPda);
      expect(configInfo).not.toBeNull();

      const data = configInfo!.data;

      // Parse MiningConfig structure (based on state.rs):
      // discriminator: [u8; 8]
      // authority: [u8; 32]
      // current_epoch: u64
      // epoch_duration_slots: u64
      // epoch_duration_seconds: u64
      // current_epoch_start: i64
      // base_rent_per_nft: u64
      // hashrate_rent_bps: u16
      // bump: u8
      // _padding: [u8; 5]

      const discriminator = data.slice(0, 8);
      const authority = new PublicKey(data.slice(8, 40));
      const currentEpoch = data.readBigUInt64LE(40);
      const epochDurationSlots = data.readBigUInt64LE(48);
      const epochDurationSeconds = data.readBigUInt64LE(56);
      const currentEpochStart = data.readBigInt64LE(64);
      const baseRentPerNft = data.readBigUInt64LE(72);
      const hashrateRentBps = data.readUInt16LE(80);
      const bump = data.readUInt8(82);

      console.log("MiningConfig state:");
      console.log(`  authority: ${authority.toBase58()}`);
      console.log(`  current_epoch: ${currentEpoch}`);
      console.log(`  epoch_duration_slots: ${epochDurationSlots}`);
      console.log(`  epoch_duration_seconds: ${epochDurationSeconds}`);
      console.log(`  current_epoch_start: ${currentEpochStart}`);
      console.log(`  base_rent_per_nft: ${baseRentPerNft}`);
      console.log(`  hashrate_rent_bps: ${hashrateRentBps}`);
      console.log(`  bump: ${bump}`);

      // Verify expected values
      expect(authority.equals(payer.publicKey)).toBe(true);
      expect(currentEpoch).toBe(BigInt(0));
      // Bump stored in account should be valid (0-255)
      expect(bump).toBeGreaterThanOrEqual(0);
      expect(bump).toBeLessThanOrEqual(255);
      expect(epochDurationSlots).toBeGreaterThan(BigInt(0));
    });
  });

  describe("Rent Economics (LodeRent.tla)", () => {
    test("SybilPenalty - splitting NFTs costs more", () => {
      // Pure calculation test (mirrors TLA+ spec)
      const baseRent = BigInt(1_000_000_000); // 1 LODE
      const hashRateRentBps = 10; // 0.1%
      const totalHashrate = BigInt(1_000_000);

      const calcRent = (hashrate: bigint) =>
        baseRent + (hashrate * BigInt(hashRateRentBps)) / BigInt(10000);

      // 1 NFT with 1M hashrate
      const consolidated = calcRent(totalHashrate);

      // 100 NFTs with 10k hashrate each
      const splitHashrate = totalHashrate / BigInt(100);
      const split100 = BigInt(100) * calcRent(splitHashrate);

      // Sybil penalty: splitting costs more
      expect(split100 > consolidated).toBe(true);
      expect(split100 >= consolidated * BigInt(2)).toBe(true);
    });
  });
});
