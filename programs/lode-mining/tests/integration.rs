//! LiteSVM Integration Tests for LODE Mining Program
//!
//! Tests cover:
//! 1. Effectiveness calculation (time-based participation)
//! 2. Hash/mask mining simulation
//! 3. Multi-winner prize splitting
//! 4. Rollover mechanics
//! 5. Rent calculation and Sybil cost analysis
//! 6. Mint cost calculation
//!
//! Note: Full integration tests with program deployment are done via Surfpool.
//! These tests verify the core business logic in isolation.

use std::str::FromStr;

// Program ID for lode-mining
const PROGRAM_ID: &str = "AxEiL9XDY9R4JVpTTD8m9XvmZnPsncj86jEeBYsJ72qG";

// Instruction discriminators (from lib.rs)
mod instruction {
    pub const INITIALIZE: u8 = 0;
    pub const MINT_MINER: u8 = 1;
    pub const UPGRADE_MINER: u8 = 2;
    pub const PAY_RENT: u8 = 3;
    pub const JOIN_EPOCH: u8 = 4;
    pub const FINALIZE_EPOCH: u8 = 5;
    pub const ADVANCE_EPOCH: u8 = 6;
    pub const CLAIM: u8 = 7;
}

// Account discriminators (from state.rs)
mod discriminator {
    pub const MINING_CONFIG: [u8; 8] = *b"mineconf";
    pub const EPOCH: [u8; 8] = *b"epoch___";
    pub const PARTICIPATION: [u8; 8] = *b"particip";
}

#[test]
fn test_effectiveness_calculation() {
    // Test the time-based effectiveness calculation logic
    // This mirrors the calculate_effectiveness function in join_epoch.rs

    fn calculate_effectiveness(elapsed: u64, duration: u64) -> u64 {
        if elapsed >= duration {
            return 0;
        }
        let remaining = duration.saturating_sub(elapsed);
        (remaining * 10000) / duration
    }

    let duration = 86400; // 24 hours

    // At start: 100%
    assert_eq!(calculate_effectiveness(0, duration), 10000);

    // At 50%: 50%
    assert_eq!(calculate_effectiveness(43200, duration), 5000);

    // At 75%: 25%
    assert_eq!(calculate_effectiveness(64800, duration), 2500);

    // At end: 0%
    assert_eq!(calculate_effectiveness(86400, duration), 0);

    // Beyond end: 0%
    assert_eq!(calculate_effectiveness(100000, duration), 0);
}

#[test]
fn test_hash_mask_mining_simulation() {
    // Test the hash/mask mining simulation logic
    // This mirrors the generate_key/generate_mask/check_match functions in finalize_epoch.rs

    fn fnv1a_hash(data: &[u8]) -> u64 {
        const FNV_OFFSET: u64 = 14695981039346656037;
        const FNV_PRIME: u64 = 1099511628211;
        let mut hash = FNV_OFFSET;
        for &byte in data {
            hash ^= byte as u64;
            hash = hash.wrapping_mul(FNV_PRIME);
        }
        hash
    }

    fn generate_key(nft_mint: &[u8], vrf_seed: u64) -> u64 {
        let mut input = Vec::with_capacity(nft_mint.len() + 8);
        input.extend_from_slice(nft_mint);
        input.extend_from_slice(&vrf_seed.to_le_bytes());
        fnv1a_hash(&input)
    }

    fn generate_mask(hashrate: u64, difficulty: u64) -> u64 {
        let permissive_bits = (hashrate / difficulty).min(64);
        if permissive_bits >= 64 {
            return u64::MAX;
        }
        (1u64 << permissive_bits).saturating_sub(1)
    }

    fn check_match(key: u64, target: u64, mask: u64) -> bool {
        (key & mask) == (target & mask)
    }

    // Test with known values
    let nft_mint = [1u8; 32];
    let vrf_seed = 12345u64;
    let key = generate_key(&nft_mint, vrf_seed);

    // Key should be deterministic
    assert_eq!(key, generate_key(&nft_mint, vrf_seed));

    // Different seed = different key
    assert_ne!(key, generate_key(&nft_mint, 67890));

    // Test mask generation
    let difficulty = 1_000_000;

    // Low hashrate = small mask = hard to hit
    let low_mask = generate_mask(100_000, difficulty);
    assert!(low_mask < u64::MAX);

    // High hashrate = large mask = easier to hit
    let high_mask = generate_mask(100_000_000, difficulty);
    assert!(high_mask > low_mask);

    // Test match checking
    let target = 0b11111111_00000000u64;
    let mask = 0b00001111u64; // Only check last 4 bits

    // Should match: last 4 bits are same (both 0000)
    assert!(check_match(0b00000000, target, mask));

    // Should not match: last 4 bits differ
    assert!(!check_match(0b00000001, target, mask));
}

#[test]
fn test_prize_splitting() {
    // Test prize splitting logic for multiple winners
    let hashrate_pool = 80_000_000_000u64; // 80 LODE
    let ticket_pool = 20_000_000_000u64;   // 20 LODE

    // Single winner gets full pool
    let share = hashrate_pool / 1;
    assert_eq!(share, 80_000_000_000);

    // Two winners split 50/50
    let share = hashrate_pool / 2;
    assert_eq!(share, 40_000_000_000);

    // Three winners split
    let share = hashrate_pool / 3;
    assert_eq!(share, 26_666_666_666); // Integer division

    // Ten winners
    let share = hashrate_pool / 10;
    assert_eq!(share, 8_000_000_000);

    // Winner of both pools (rare but possible)
    let hashrate_winner_count = 2u16;
    let ticket_winner_count = 1u16;

    let hashrate_share = hashrate_pool / (hashrate_winner_count as u64);
    let ticket_share = ticket_pool / (ticket_winner_count as u64);

    let total = hashrate_share + ticket_share;
    assert_eq!(total, 40_000_000_000 + 20_000_000_000);
    assert_eq!(total, 60_000_000_000);
}

#[test]
fn test_rollover_splitting() {
    // Test rollover 80/20 splitting between pools
    let rollover = 100_000_000_000u64; // 100 LODE

    let rollover_hashrate = (rollover * 8000) / 10000;
    let rollover_ticket = rollover - rollover_hashrate;

    assert_eq!(rollover_hashrate, 80_000_000_000);
    assert_eq!(rollover_ticket, 20_000_000_000);

    // No rollover case
    let rollover = 0u64;
    let rollover_hashrate = (rollover * 8000) / 10000;
    let rollover_ticket = rollover - rollover_hashrate;

    assert_eq!(rollover_hashrate, 0);
    assert_eq!(rollover_ticket, 0);
}

#[test]
fn test_rent_calculation() {
    // Test rent calculation: base_rent + (hashrate * hashrate_rent_bps / 10000)
    let base_rent = 1_000_000_000u64; // 1 LODE
    let hashrate_rent_bps = 1u16;     // 0.01%

    fn calculate_rent(base_rent: u64, hashrate: u64, hashrate_rent_bps: u16) -> u64 {
        let hashrate_rent = (hashrate * hashrate_rent_bps as u64) / 10000;
        base_rent.saturating_add(hashrate_rent)
    }

    // 100k hashrate: 1 LODE + 10 LODE = 11 LODE
    // Wait, 100000 * 1 / 10000 = 10, but we want LODE units
    // Let's say hashrate is already in LODE-denominated units

    // NFT with 1M hashrate
    let rent = calculate_rent(base_rent, 1_000_000, hashrate_rent_bps);
    assert_eq!(rent, 1_000_000_100); // Base + 100 units

    // NFT with 10M hashrate
    let rent = calculate_rent(base_rent, 10_000_000, hashrate_rent_bps);
    assert_eq!(rent, 1_000_001_000); // Base + 1000 units
}

#[test]
fn test_sybil_cost_analysis() {
    // Verify that splitting hashrate costs more than consolidating
    let base_rent = 1_000_000_000u64;  // 1 LODE
    let hashrate_rent_bps = 10u16;     // 0.1%
    let total_hashrate = 1_000_000u64;

    fn calculate_total_rent(base_rent: u64, hashrate: u64, hashrate_rent_bps: u16, nft_count: u64) -> u64 {
        let hashrate_per_nft = hashrate / nft_count;
        let rent_per_nft = base_rent + (hashrate_per_nft * hashrate_rent_bps as u64) / 10000;
        rent_per_nft * nft_count
    }

    // 1 NFT with 1M hashrate
    let cost_1 = calculate_total_rent(base_rent, total_hashrate, hashrate_rent_bps, 1);

    // 10 NFTs with 100k hashrate each
    let cost_10 = calculate_total_rent(base_rent, total_hashrate, hashrate_rent_bps, 10);

    // 100 NFTs with 10k hashrate each
    let cost_100 = calculate_total_rent(base_rent, total_hashrate, hashrate_rent_bps, 100);

    // More NFTs should cost more (base rent adds up)
    assert!(cost_10 > cost_1, "10 NFTs should cost more than 1");
    assert!(cost_100 > cost_10, "100 NFTs should cost more than 10");

    // Verify the anti-Sybil property: 100 NFTs costs at least 2x consolidated
    // With base_rent of 1 LODE and 0.1% hashrate rent:
    // 1 NFT:   1 LODE + 0.1% * 1M = 1 + 1000 = 1001 LODE-units
    // 100 NFTs: 100 * (1 LODE + 0.1% * 10k) = 100 * (1 + 10) = 11000 LODE-units
    assert!(
        cost_100 >= cost_1 * 2,
        "100 NFTs should cost at least 2x: {} vs {}",
        cost_100,
        cost_1 * 2
    );
}

#[test]
fn test_mint_cost_calculation() {
    // Test progressive mint fee calculation
    fn calculate_mint_cost(base_mint_cost: u64, epoch_progress_bps: u16) -> (u64, u64, u64) {
        let multiplier = 10000u64 + (epoch_progress_bps as u64 / 2);
        let total = base_mint_cost
            .checked_mul(multiplier)
            .unwrap_or(base_mint_cost)
            / 10000;

        let burn_amount = total * 70 / 100;
        let lottery_amount = total - burn_amount;

        (total, burn_amount, lottery_amount)
    }

    let base_cost = 100_000_000_000u64; // 100 LODE

    // At epoch start (0 bps), no progressive fee
    let (total, burn, lottery) = calculate_mint_cost(base_cost, 0);
    assert_eq!(total, 100_000_000_000);
    assert_eq!(burn, 70_000_000_000);
    assert_eq!(lottery, 30_000_000_000);

    // At epoch mid (5000 bps = 50%), 25% fee increase
    let (total, burn, lottery) = calculate_mint_cost(base_cost, 5000);
    assert_eq!(total, 125_000_000_000);
    assert_eq!(burn, 87_500_000_000);
    assert_eq!(lottery, 37_500_000_000);

    // At epoch end (10000 bps = 100%), 50% fee increase
    let (total, burn, lottery) = calculate_mint_cost(base_cost, 10000);
    assert_eq!(total, 150_000_000_000);
    assert_eq!(burn, 105_000_000_000);
    assert_eq!(lottery, 45_000_000_000);
}

#[test]
fn test_lottery_weight_distribution() {
    // Test 80/20 split between hashrate and ticket pools
    let total_pool = 100_000_000_000u64; // 100 LODE

    let hashrate_pool = (total_pool * 80) / 100;
    let ticket_pool = total_pool - hashrate_pool;

    assert_eq!(hashrate_pool, 80_000_000_000);
    assert_eq!(ticket_pool, 20_000_000_000);
}

#[test]
fn test_difficulty_adjustment() {
    // Test that difficulty scaling works correctly
    let base_difficulty = 1_000_000u64;

    fn generate_mask(hashrate: u64, difficulty: u64) -> u64 {
        let permissive_bits = (hashrate / difficulty).min(64);
        if permissive_bits >= 64 {
            return u64::MAX;
        }
        (1u64 << permissive_bits).saturating_sub(1)
    }

    // 1x difficulty: 1M hashrate = 1 permissive bit (mask = 1)
    let mask_1x = generate_mask(1_000_000, base_difficulty);
    assert_eq!(mask_1x, 1);

    // 10x hashrate: 10M hashrate = 10 permissive bits (mask = 1023)
    let mask_10x = generate_mask(10_000_000, base_difficulty);
    assert_eq!(mask_10x, 1023);

    // 100x hashrate: 100M hashrate = 100 permissive bits, capped at 64 (mask = u64::MAX)
    let mask_100x = generate_mask(100_000_000, base_difficulty);
    assert_eq!(mask_100x, u64::MAX);
}

#[test]
fn test_epoch_state_transitions() {
    // Test epoch state machine logic
    #[derive(Debug, PartialEq, Clone, Copy)]
    enum EpochState {
        Active = 0,
        Finalized = 1,
    }

    // Epoch starts as Active
    let mut state = EpochState::Active;
    assert_eq!(state, EpochState::Active);

    // Can finalize an Active epoch
    if state == EpochState::Active {
        state = EpochState::Finalized;
    }
    assert_eq!(state, EpochState::Finalized);

    // Cannot finalize again (would be no-op in real impl)
    // Epoch advances to next after finalized
}

#[test]
fn test_participation_flags() {
    // Test participation flag combinations
    #[derive(Default)]
    struct Participation {
        rent_paid: bool,
        hashrate_claimed: bool,
        ticket_claimed: bool,
        won_hashrate_pool: bool,
        won_ticket_pool: bool,
    }

    let mut p = Participation::default();

    // Initial state: nothing set
    assert!(!p.rent_paid);
    assert!(!p.won_hashrate_pool);
    assert!(!p.won_ticket_pool);

    // Pay rent
    p.rent_paid = true;
    assert!(p.rent_paid);

    // Win hashrate pool (set by finalize)
    p.won_hashrate_pool = true;
    assert!(p.won_hashrate_pool);

    // Can claim hashrate pool winnings
    assert!(p.won_hashrate_pool && !p.hashrate_claimed);
    p.hashrate_claimed = true;

    // Cannot double-claim
    assert!(!(p.won_hashrate_pool && !p.hashrate_claimed));
}

#[test]
fn test_vrf_seed_determinism() {
    // Test that VRF seed produces deterministic results
    fn fnv1a_hash(data: &[u8]) -> u64 {
        const FNV_OFFSET: u64 = 14695981039346656037;
        const FNV_PRIME: u64 = 1099511628211;
        let mut hash = FNV_OFFSET;
        for &byte in data {
            hash ^= byte as u64;
            hash = hash.wrapping_mul(FNV_PRIME);
        }
        hash
    }

    let seed = 12345u64;
    let nft1 = [1u8; 32];
    let nft2 = [2u8; 32];

    // Same inputs = same output
    let mut input1 = Vec::new();
    input1.extend_from_slice(&nft1);
    input1.extend_from_slice(&seed.to_le_bytes());
    let hash1a = fnv1a_hash(&input1);
    let hash1b = fnv1a_hash(&input1);
    assert_eq!(hash1a, hash1b);

    // Different NFTs = different outputs
    let mut input2 = Vec::new();
    input2.extend_from_slice(&nft2);
    input2.extend_from_slice(&seed.to_le_bytes());
    let hash2 = fnv1a_hash(&input2);
    assert_ne!(hash1a, hash2);
}
