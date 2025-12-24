//! Finalize epoch instruction
//!
//! Hash/mask-based mining simulation to select winners.
//! - VRF generates a random "target" each epoch
//! - Each NFT's hashrate determines mask permissiveness
//! - Multiple winners possible (prize split) or no winner (rollover to next epoch)
//!
//! For MVP, we use slot hash as pseudo-random source. Production will use Switchboard VRF.
//!
//! Accounts:
//! 0. [signer] Payer (crank)
//! 1. [] MiningConfig PDA
//! 2. [writable] Epoch PDA
//! 3. [] Slot hashes sysvar (for pseudo-randomness)
//! Plus: N participation accounts to iterate through for winner selection

use crate::{
    error::MiningError,
    state::{Epoch, EpochParticipation, MiningConfig},
};
use pinocchio::{
    account_info::AccountInfo,
    program_error::ProgramError,
    pubkey::Pubkey,
    sysvars::{clock::Clock, Sysvar},
    ProgramResult,
};

/// FNV-1a hash function for pseudo-randomness
fn fnv_hash(data: &[u8]) -> u64 {
    let mut hash: u64 = 0xcbf29ce484222325; // FNV offset basis
    for byte in data {
        hash ^= *byte as u64;
        hash = hash.wrapping_mul(0x100000001b3); // FNV prime
    }
    hash
}

/// Generate a "key" for an NFT based on its mint and the VRF seed
/// key = hash(nft_mint || vrf_seed)
fn generate_key(nft_mint: &[u8], vrf_seed: u64) -> u64 {
    let mut input = [0u8; 40];
    input[0..32].copy_from_slice(nft_mint);
    input[32..40].copy_from_slice(&vrf_seed.to_le_bytes());
    fnv_hash(&input)
}

/// Calculate mining mask from hashrate
/// Higher hashrate = more permissive mask (more 1 bits)
/// mask_bits = log2(hashrate / difficulty) bits set to 1
///
/// Example with difficulty = 1_000_000:
/// - hashrate 1M: ~0 permissive bits (exact match needed)
/// - hashrate 10M: ~3 permissive bits
/// - hashrate 100M: ~6 permissive bits
/// - hashrate 1B: ~10 permissive bits
fn calculate_mask(weighted_hashrate: u64, difficulty: u64) -> u64 {
    if weighted_hashrate == 0 || difficulty == 0 {
        return 0; // No permissiveness
    }

    // ratio = hashrate / difficulty
    // permissive_bits = floor(log2(ratio))
    let ratio = weighted_hashrate.saturating_div(difficulty);
    if ratio <= 1 {
        return 0; // Need exact match
    }

    // Calculate log2(ratio) using leading zeros
    let log2_ratio = 63 - ratio.leading_zeros() as u64;

    // Create mask with log2_ratio least significant bits set
    // e.g., log2_ratio = 3 -> mask = 0b111 = 7
    if log2_ratio >= 64 {
        return u64::MAX;
    }
    (1u64 << log2_ratio).saturating_sub(1)
}

/// Check if a key "hits" the target within the mask
/// A hit occurs when: (key XOR target) & ~mask == 0
/// This means all non-masked bits must match exactly
#[inline]
fn check_hit(key: u64, target: u64, mask: u64) -> bool {
    let diff = key ^ target;
    let strict_mask = !mask;
    (diff & strict_mask) == 0
}

/// Check if participant data is valid for this epoch
/// Returns true if: correct discriminator, rent paid, matching epoch
#[inline]
fn is_valid_participant(part_data: &[u8], epoch_id: u64) -> bool {
    // Check size
    if part_data.len() < EpochParticipation::SIZE {
        return false;
    }
    // Check discriminator
    if part_data[0..8] != EpochParticipation::DISCRIMINATOR {
        return false;
    }
    // Check rent paid (byte 112)
    if part_data[112] == 0 {
        return false;
    }
    // Check epoch matches
    let part_epoch_id = u64::from_le_bytes(
        match part_data[8..16].try_into() {
            Ok(bytes) => bytes,
            Err(_) => return false,
        }
    );
    part_epoch_id == epoch_id
}

/// Process finalize_epoch instruction
///
/// Uses hash/mask mining simulation:
/// 1. Generate target from VRF seed
/// 2. For each participant, check if their "key" hits the target
/// 3. Mark winners in their participation accounts
/// 4. If no winners, pools roll over to next epoch
pub fn process(program_id: &Pubkey, accounts: &[AccountInfo], _data: &[u8]) -> ProgramResult {
    // Minimum 4 accounts: payer, config, epoch, slot_hashes
    if accounts.len() < 4 {
        return Err(ProgramError::NotEnoughAccountKeys);
    }

    let payer = &accounts[0];
    let config_account = &accounts[1];
    let epoch_account = &accounts[2];
    let slot_hashes = &accounts[3];
    let participants = &accounts[4..];

    // Validate payer is signer
    if !payer.is_signer() {
        return Err(MiningError::AccountNotSigner.into());
    }

    // Validate epoch is writable
    if !epoch_account.is_writable() {
        return Err(MiningError::AccountNotWritable.into());
    }

    // Validate config account
    let config_data = unsafe { config_account.borrow_data_unchecked() };
    if config_data.len() < MiningConfig::SIZE {
        return Err(MiningError::InvalidAccountData.into());
    }
    if config_data[0..8] != MiningConfig::DISCRIMINATOR {
        return Err(MiningError::InvalidPdaSeeds.into());
    }

    // Read effective hashrate cap (bytes 87-95, 0 = no cap)
    let effective_hashrate_cap = u64::from_le_bytes(
        config_data[87..95]
            .try_into()
            .map_err(|_| MiningError::InvalidAccountData)?,
    );

    // Validate epoch account
    let epoch_data = unsafe { epoch_account.borrow_mut_data_unchecked() };
    if epoch_data.len() < Epoch::SIZE {
        return Err(MiningError::InvalidAccountData.into());
    }
    if epoch_data[0..8] != Epoch::DISCRIMINATOR {
        return Err(MiningError::InvalidPdaSeeds.into());
    }

    // Check epoch is active (not already finalized)
    let epoch_state = epoch_data[60];
    if epoch_state != Epoch::STATE_ACTIVE {
        if epoch_state == Epoch::STATE_FINALIZED {
            return Err(MiningError::EpochAlreadyFinalized.into());
        }
        return Err(MiningError::EpochNotActive.into());
    }

    // Check epoch has ended
    let end_timestamp = i64::from_le_bytes(
        epoch_data[24..32]
            .try_into()
            .map_err(|_| MiningError::InvalidAccountData)?,
    );

    let clock = Clock::get()?;
    let now = clock.unix_timestamp;

    if now < end_timestamp {
        return Err(MiningError::EpochNotActive.into());
    }

    let epoch_id = u64::from_le_bytes(
        epoch_data[8..16]
            .try_into()
            .map_err(|_| MiningError::InvalidAccountData)?,
    );

    // Get prize pools
    let hashrate_pool = u64::from_le_bytes(
        epoch_data[32..40]
            .try_into()
            .map_err(|_| MiningError::InvalidAccountData)?,
    );
    let ticket_pool = u64::from_le_bytes(
        epoch_data[40..48]
            .try_into()
            .map_err(|_| MiningError::InvalidAccountData)?,
    );

    // Get difficulty (default if not set)
    let difficulty = u64::from_le_bytes(
        epoch_data[80..88]
            .try_into()
            .map_err(|_| MiningError::InvalidAccountData)?,
    );
    let difficulty = if difficulty == 0 { Epoch::DEFAULT_DIFFICULTY } else { difficulty };

    // Generate VRF seed from slot hashes
    let slot_data = unsafe { slot_hashes.borrow_data_unchecked() };
    let mut seed_input = [0u8; 40];
    seed_input[0..8].copy_from_slice(&epoch_id.to_le_bytes());
    seed_input[8..16].copy_from_slice(&now.to_le_bytes());
    if slot_data.len() >= 24 {
        seed_input[16..40].copy_from_slice(&slot_data[0..24]);
    }
    let vrf_seed = fnv_hash(&seed_input);

    // The "target" is derived from VRF seed
    let target = fnv_hash(&vrf_seed.to_le_bytes());

    // Pass 1: Count valid participants and find hashrate pool winners
    // We iterate through participants, check for hits, and mark winners
    let mut hashrate_winner_count: u16 = 0;
    let mut ticket_winner_count: u16 = 0;
    let mut total_weighted_hashrate = 0u64;

    // For ticket pool: uniform random selection
    // We'll use a second pass if needed
    let mut valid_count = 0u64;

    // First, count valid participants and compute ticket pool winner index
    for participant_account in participants.iter() {
        let part_data = unsafe { participant_account.borrow_data_unchecked() };
        if !is_valid_participant(part_data, epoch_id) {
            continue;
        }

        let weighted_hashrate = u64::from_le_bytes(
            part_data[104..112]
                .try_into()
                .map_err(|_| MiningError::InvalidAccountData)?,
        );

        total_weighted_hashrate = total_weighted_hashrate.saturating_add(weighted_hashrate);
        valid_count += 1;
    }

    // Generate ticket pool target (different from hashrate target)
    let ticket_target = fnv_hash(&[&vrf_seed.to_le_bytes()[..], b"ticket"].concat());
    // For ticket pool: simpler check - each participant has 1/N chance
    // We use a threshold: if hash(nft || ticket_target) < u64::MAX / valid_count, they win
    let ticket_threshold = if valid_count > 0 {
        u64::MAX / valid_count
    } else {
        0
    };

    // Pass 2: Mark winners (requires writable participation accounts)
    for participant_account in participants.iter() {
        if !participant_account.is_writable() {
            continue;
        }

        let part_data = unsafe { participant_account.borrow_mut_data_unchecked() };
        if !is_valid_participant(part_data, epoch_id) {
            continue;
        }

        // Get NFT mint (bytes 16-48) - copy to avoid borrow issues
        let mut nft_mint = [0u8; 32];
        nft_mint.copy_from_slice(&part_data[16..48]);

        // Get weighted hashrate
        let weighted_hashrate = u64::from_le_bytes(
            part_data[104..112]
                .try_into()
                .map_err(|_| MiningError::InvalidAccountData)?,
        );

        // Apply hashrate cap for fair distribution
        let capped_hashrate = if effective_hashrate_cap > 0 {
            weighted_hashrate.min(effective_hashrate_cap)
        } else {
            weighted_hashrate
        };

        // Check hashrate pool winner (mask-based)
        let key = generate_key(&nft_mint, vrf_seed);
        let mask = calculate_mask(capped_hashrate, difficulty);

        if check_hit(key, target, mask) && hashrate_winner_count < Epoch::MAX_WINNERS_PER_POOL {
            // Mark as hashrate pool winner (byte 116)
            part_data[116] = 1;
            hashrate_winner_count += 1;
        }

        // Check ticket pool winner (uniform random)
        let ticket_key = generate_key(&nft_mint, ticket_target);
        if ticket_key < ticket_threshold && ticket_winner_count < Epoch::MAX_WINNERS_PER_POOL {
            // Mark as ticket pool winner (byte 117)
            part_data[117] = 1;
            ticket_winner_count += 1;
        }
    }

    // Calculate rollover if no winners
    let mut rollover_amount = 0u64;
    if hashrate_winner_count == 0 {
        rollover_amount = rollover_amount.saturating_add(hashrate_pool);
    }
    if ticket_winner_count == 0 {
        rollover_amount = rollover_amount.saturating_add(ticket_pool);
    }

    // Update epoch data
    // state = finalized (byte 60)
    epoch_data[60] = Epoch::STATE_FINALIZED;

    // vrf_seed (bytes 62-70) - note: shifted due to removed winner pubkeys
    epoch_data[62..70].copy_from_slice(&vrf_seed.to_le_bytes());

    // total_weighted_hashrate (bytes 70-78)
    epoch_data[70..78].copy_from_slice(&total_weighted_hashrate.to_le_bytes());

    // difficulty (bytes 78-86) - store what was used
    epoch_data[78..86].copy_from_slice(&difficulty.to_le_bytes());

    // hashrate_winner_count (bytes 86-88)
    epoch_data[86..88].copy_from_slice(&hashrate_winner_count.to_le_bytes());

    // ticket_winner_count (bytes 88-90)
    epoch_data[88..90].copy_from_slice(&ticket_winner_count.to_le_bytes());

    // rollover_amount (bytes 56-64) - stored for next epoch to pick up
    epoch_data[56..64].copy_from_slice(&rollover_amount.to_le_bytes());

    // Verify owner
    if epoch_account.owner() != program_id {
        return Err(MiningError::InvalidAuthority.into());
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fnv_hash() {
        let data1 = b"test1";
        let data2 = b"test2";

        let hash1 = fnv_hash(data1);
        let hash2 = fnv_hash(data2);

        // Different inputs should produce different hashes
        assert_ne!(hash1, hash2);

        // Same input should produce same hash
        assert_eq!(fnv_hash(data1), fnv_hash(data1));
    }

    #[test]
    fn test_calculate_mask() {
        let difficulty = 1_000_000u64;

        // hashrate == difficulty: ratio = 1, no permissive bits
        let mask = calculate_mask(1_000_000, difficulty);
        assert_eq!(mask, 0);

        // hashrate = 2x difficulty: ratio = 2, log2(2) = 1 bit
        let mask = calculate_mask(2_000_000, difficulty);
        assert_eq!(mask, 1); // 0b1

        // hashrate = 4x difficulty: ratio = 4, log2(4) = 2 bits
        let mask = calculate_mask(4_000_000, difficulty);
        assert_eq!(mask, 3); // 0b11

        // hashrate = 8x difficulty: ratio = 8, log2(8) = 3 bits
        let mask = calculate_mask(8_000_000, difficulty);
        assert_eq!(mask, 7); // 0b111

        // hashrate = 1024x difficulty: ratio = 1024, log2(1024) = 10 bits
        let mask = calculate_mask(1_024_000_000, difficulty);
        assert_eq!(mask, 1023); // 0b1111111111
    }

    #[test]
    fn test_check_hit() {
        // Exact match (no mask)
        let key = 0x1234567890abcdef;
        let target = 0x1234567890abcdef;
        let mask = 0; // No permissive bits
        assert!(check_hit(key, target, mask));

        // Near match with mask
        let key = 0x1234567890abcdef;
        let target = 0x1234567890abcde0; // Last nibble differs
        let mask = 0xF; // Last 4 bits permissive
        assert!(check_hit(key, target, mask));

        // Miss (difference outside mask)
        let key = 0x1234567890abcdef;
        let target = 0x1234567890ab0def; // Middle byte differs
        let mask = 0xF; // Only last 4 bits permissive
        assert!(!check_hit(key, target, mask));
    }

    #[test]
    fn test_generate_key() {
        let mint1 = [1u8; 32];
        let mint2 = [2u8; 32];
        let seed = 12345u64;

        let key1 = generate_key(&mint1, seed);
        let key2 = generate_key(&mint2, seed);

        // Different mints should produce different keys
        assert_ne!(key1, key2);

        // Same mint + seed should produce same key
        assert_eq!(generate_key(&mint1, seed), generate_key(&mint1, seed));

        // Different seeds should produce different keys
        assert_ne!(generate_key(&mint1, seed), generate_key(&mint1, seed + 1));
    }

    #[test]
    fn test_mining_simulation() {
        // Simulate 10 miners with varying hashrates
        let difficulty = 1_000_000u64;
        let vrf_seed = 0xdeadbeef12345678u64;
        let target = fnv_hash(&vrf_seed.to_le_bytes());

        let miners = [
            ([1u8; 32], 500_000u64),    // Low hashrate
            ([2u8; 32], 1_000_000u64),  // Equal to difficulty
            ([3u8; 32], 2_000_000u64),  // 2x difficulty
            ([4u8; 32], 4_000_000u64),  // 4x difficulty
            ([5u8; 32], 8_000_000u64),  // 8x difficulty
            ([6u8; 32], 16_000_000u64), // 16x difficulty
            ([7u8; 32], 32_000_000u64), // 32x difficulty
            ([8u8; 32], 64_000_000u64), // 64x difficulty
            ([9u8; 32], 128_000_000u64),// 128x difficulty
            ([10u8; 32], 256_000_000u64),// 256x difficulty
        ];

        let mut winners = Vec::new();
        for (mint, hashrate) in miners.iter() {
            let key = generate_key(mint, vrf_seed);
            let mask = calculate_mask(*hashrate, difficulty);
            if check_hit(key, target, mask) {
                winners.push((*mint, *hashrate));
            }
        }

        // With this particular seed, we might have 0, 1, or multiple winners
        // This is expected behavior - print for visibility
        println!("Target: {:016x}", target);
        println!("Winners: {}", winners.len());
        for (mint, hr) in &winners {
            println!("  Mint[0]={}, Hashrate={}", mint[0], hr);
        }

        // The test passes regardless of winner count - that's the game!
        // Higher hashrate = higher probability, but no guarantee
    }
}
