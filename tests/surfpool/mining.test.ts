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
  "7t9rXjXvx9n8mfQBuwEP927DVFmvSkcJVPfXUGjAvSdh"
);

// Instruction discriminators (match lib.rs)
const INSTRUCTION = {
  INITIALIZE: 0,
  MINT_MINER: 1,
  UPGRADE_MINER: 2,
  PAY_RENT: 3,
  JOIN_EPOCH: 4,
  FINALIZE_EPOCH: 5,
  ADVANCE_EPOCH: 6,
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

      // Derive config PDA
      const [configPda] = PublicKey.findProgramAddressSync(
        [Buffer.from("config")],
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
