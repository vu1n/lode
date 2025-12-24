# LODE Protocol v2

NFT-based mining protocol on Solana. Mint NFT miners, earn hashrate, win LODE in daily lottery drawings.

## Overview

LODE is a deflationary token protocol where users compete for lottery prizes by staking NFT miners. Every action—minting, upgrading, paying rent—burns tokens, creating sustainable deflation while rewarding active participants.

**Core Loop:**
1. Mint an NFT miner (burns 70% of cost, 30% to lottery pool)
2. Join daily epochs and pay rent to participate
3. Win LODE from dual lottery pools (hashrate-weighted + random)
4. Upgrade miners to increase odds over time

## Design Philosophy

### The Balance Problem

Most token protocols face a dilemma:
- **Pure linear scaling** → Whales dominate, small fish leave
- **Aggressive diminishing returns** → Whales sybil into many wallets, gaming the curve

LODE solves this with **per-NFT caps** instead of per-wallet curves:

```
effective_hashrate = min(actual_hashrate, cap)
```

### Why This Works

| Player | Strategy | Outcome |
|--------|----------|---------|
| Small fish | One miner, grind to cap | Competitive lottery odds |
| Whale | Many miners at cap | More odds, but pays more rent & burns more LODE |
| Sybil attacker | Split wallet | No benefit (cap is per-NFT, not per-wallet) |

**The insight:** By making the NFT the unit of account (not the wallet), we eliminate sybil incentives while keeping whales engaged. Whales who want more lottery power must:
1. Mint more NFTs (burns 70% of mint cost)
2. Pay rent on each NFT (burns 70% of rent)
3. Manage more assets

This transforms whale accumulation from a zero-sum game into **protocol-aligned behavior** that increases deflation.

## Programs

| Program | Address | Purpose |
|---------|---------|---------|
| lode-token | `ANxSnSKr6VBXw7dEaW9P3utWbXxoH2jxctgA1sXtPyL8` | Token-2022 mint with 0.5% transfer fee |
| lode-treasury | `HjRCbiKYNa61Mee6Hbxy5tGCPzDBrzNcaZjVRGcPcSFC` | Fee harvesting & distribution (30/50/20 split) |
| lode-mining | `CSrYQ2uEURizXFDruLVyHUXcNN1Dv3XKFdbPnddMF2pB` | NFT miners, epochs, lottery engine |

## How Mining Works

### NFT Miners

Each miner is a Metaplex Core NFT with on-chain attributes:

- **Hashrate** — Determines lottery odds (higher = better)
- **Age** — Epochs since creation (+1% bonus per epoch, max +50%)
- **Total Burned** — Cumulative LODE spent on this miner

### Epoch Lifecycle (24 hours)

```
┌─────────────────────────────────────────────────────────────┐
│                        EPOCH N                               │
├──────────────────┬──────────────────┬───────────────────────┤
│   JOIN PHASE     │   RENT WINDOW    │   FINALIZATION        │
│   (anytime)      │   (first 10%)    │   (after end)         │
├──────────────────┼──────────────────┼───────────────────────┤
│ • join_epoch()   │ • pay_rent()     │ • finalize_epoch()    │
│ • Snapshot       │ • Required for   │ • VRF → winners       │
│   hashrate       │   eligibility    │ • advance_epoch()     │
│ • Earlier =      │                  │ • claim() prizes      │
│   higher weight  │                  │                       │
└──────────────────┴──────────────────┴───────────────────────┘
```

**Time Effectiveness:** Joining early maximizes your weighted hashrate. Join at hour 0 = 100% weight. Join at hour 12 = 50% weight. Join at hour 23 = ~4% weight.

### Dual Lottery Pools

Each epoch has two prize pools:

| Pool | Share | Selection Method |
|------|-------|------------------|
| Hashrate Pool | 80% | Hash/mask mining (favors high hashrate) |
| Ticket Pool | 20% | Uniform random (equal odds for all) |

**Hash/Mask Mining:** For each NFT, we compute `key = hash(nft_mint || vrf_seed)` and check if it matches the random target within a mask. Higher hashrate = more permissive mask = higher win probability.

### Per-NFT Hashrate Cap

To keep small participants competitive and prevent whale dominance:

```
effective_hashrate = min(hashrate, cap)
```

**Why this matters:**
- Each NFT's lottery odds are capped at a maximum effective hashrate
- Small fish can reach the cap and compete on equal footing
- Whales who want more odds must mint multiple NFTs (burns more LODE)
- No sybil incentive—the cap is per-NFT, not per-wallet

**The economics flip:** Whales now drive *more* deflation by minting multiple NFTs to scale, while paying rent on each one.

## Tokenomics

### Fee Flows

**On Mint/Upgrade/Rent:**
```
User pays LODE → 70% BURNED → 30% to Lottery Pool
```

**On Transfer (0.5% fee):**
```
Transfer fee → Treasury → 30% burn / 50% lottery / 20% POL
```

### Emission Schedule

| Phase | Duration | Emission |
|-------|----------|----------|
| Halving | Years 1-8 | 40,000 LODE/week initial, halving every 4 years |
| Tail | Year 8+ | 0.3% of supply per year |

**Hard Cap:** 21,000,000 LODE (9 decimals)

### Sybil Resistance

Splitting stake across wallets is unprofitable:
- Transfer fees (0.5%) penalize moving tokens
- No hashrate bonus from wallet splitting
- Age bonus rewards consolidation (+1%/epoch on single NFT)
- Rent scales with hashrate (high-power miners pay more)

## Parameters

| Parameter | Value | Description |
|-----------|-------|-------------|
| Epoch Duration | 24 hours | Lottery cycle length |
| Base Rent | 1 LODE | Minimum rent per NFT |
| Hashrate Rent | 0.01% | Additional rent based on hashrate |
| Grace Period | 10% | Rent payment window (2.4 hours) |
| Age Bonus | +1%/epoch | Max +50% bonus for veteran miners |
| Base Mint Cost | 100 LODE | Starting cost for new miner |
| Difficulty | 1,000,000 | Mining difficulty calibration |
| Hashrate Cap | 100M | Max effective hashrate per NFT for lottery |

## Development

### Build

```bash
# Docker build (produces SBF binaries)
docker compose run --rm build

# Output: target/deploy/*.so
```

### Testing Strategy

**LiteSVM → Surfpool → Devnet**

```bash
# 1. Unit tests (fast, in-process)
cargo test --package lode-mining

# 2. Integration tests (local validator)
surfpool start --no-tui
bun test tests/surfpool/

# 3. Devnet deployment
solana program deploy target/deploy/lode_mining.so \
  --program-id keypairs/lode-mining-keypair.json
```

### Project Structure

```
lode/
├── programs/
│   ├── lode-token/      # Token-2022 mint
│   ├── lode-treasury/   # Fee distribution
│   └── lode-mining/     # NFT miners & lottery
├── tests/
│   └── surfpool/        # Integration tests
├── specs/               # TLA+ formal specifications
├── keypairs/            # Program keypairs
├── Surfpool.toml        # Local validator config
└── Cargo.toml           # Rust workspace
```

### Dependencies

All programs use [Pinocchio](https://github.com/anza-xyz/pinocchio) (lightweight Solana framework):

```toml
pinocchio = "0.9"
pinocchio-system = "0.4"
pinocchio-pubkey = "0.3"
```

NFTs use Metaplex Core for on-chain attributes.

## Formal Specifications

TLA+ specs in `/specs/` provide formal verification of:

- `LodeMining.tla` — Core staking & lottery invariants
- `LodeEmissions.tla` — Emission schedule correctness
- `LodeEpoch.tla` — Epoch state transitions
- `LodeLottery.tla` — Winner selection fairness
- `LodeRent.tla` — Rent calculation mechanics

## Architecture Highlights

- **Permissionless Operations** — Anyone can call `advance_epoch()` and `finalize_epoch()`
- **Rollover Mechanics** — Unclaimed prizes roll to the next epoch
- **Prize Splitting** — Multiple winners split pool equally
- **O(n) Mining Simulation** — Elegant hash/mask approach, no per-participant VRF calls
- **On-Chain Randomness** — Uses slot hashes (production: Switchboard VRF)
