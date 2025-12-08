//! Join epoch instruction
//!
//! Registers an NFT miner for the current epoch lottery.
//! Creates an EpochParticipation PDA to track participation.
//! Time-based effectiveness: joining late = reduced hashrate for this epoch.
//!
//! Accounts:
//! 0. [signer] Owner/authority
//! 1. [] MiningConfig PDA
//! 2. [writable] Epoch PDA
//! 3. [writable] EpochParticipation PDA (to be created)
//! 4. [] NFT asset account
//! 5. [] System program

use crate::{
    error::MiningError,
    mpl_core::parse_miner_attributes,
    state::{Epoch, EpochParticipation, MiningConfig},
};
use pinocchio::{
    account_info::AccountInfo,
    instruction::{Seed, Signer},
    program_error::ProgramError,
    pubkey::{find_program_address, Pubkey},
    sysvars::{clock::Clock, Sysvar},
    ProgramResult,
};

/// Calculate time-based effectiveness
/// Joining at hour 0: 100% hashrate
/// Joining at hour 12: 50% hashrate
/// Joining at hour 23: ~4% hashrate
pub fn calculate_effectiveness(elapsed: u64, duration: u64) -> u64 {
    if elapsed >= duration {
        return 0;
    }
    let remaining = duration.saturating_sub(elapsed);
    // Return percentage in basis points (10000 = 100%)
    (remaining * 10000) / duration
}

/// Process join_epoch instruction
pub fn process(program_id: &Pubkey, accounts: &[AccountInfo], _data: &[u8]) -> ProgramResult {
    let [owner, config_account, epoch_account, participation_account, nft_asset, _system_program] =
        accounts
    else {
        return Err(ProgramError::NotEnoughAccountKeys);
    };

    // Validate owner is signer
    if !owner.is_signer() {
        return Err(MiningError::AccountNotSigner.into());
    }

    // Validate participation is writable
    if !participation_account.is_writable() {
        return Err(MiningError::AccountNotWritable.into());
    }

    // Validate epoch is writable (need to update counters)
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

    let epoch_duration = u64::from_le_bytes(
        config_data[48..56]
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

    // Check epoch is active (byte 60 in new layout)
    let epoch_state = epoch_data[60];
    if epoch_state != Epoch::STATE_ACTIVE {
        return Err(MiningError::EpochNotActive.into());
    }

    let epoch_id = u64::from_le_bytes(
        epoch_data[8..16]
            .try_into()
            .map_err(|_| MiningError::InvalidAccountData)?,
    );
    let start_timestamp = i64::from_le_bytes(
        epoch_data[16..24]
            .try_into()
            .map_err(|_| MiningError::InvalidAccountData)?,
    );

    // Get current time
    let clock = Clock::get()?;
    let now = clock.unix_timestamp;
    let elapsed = now.saturating_sub(start_timestamp) as u64;

    // Get hashrate from NFT
    let nft_data = unsafe { nft_asset.borrow_data_unchecked() };
    let (hashrate, _, _, _) =
        parse_miner_attributes(&nft_data).ok_or(MiningError::InvalidAccountData)?;

    // Calculate effective hashrate based on time remaining
    let effectiveness_bps = calculate_effectiveness(elapsed, epoch_duration);
    let effective_hashrate = (hashrate * effectiveness_bps) / 10000;

    // Derive participation PDA seeds
    let epoch_id_bytes = epoch_id.to_le_bytes();
    let seeds = &[
        EpochParticipation::SEEDS_PREFIX,
        &epoch_id_bytes,
        nft_asset.key().as_ref(),
    ];
    let (expected_pda, bump) = find_program_address(seeds, program_id);

    if participation_account.key() != &expected_pda {
        return Err(MiningError::InvalidPdaSeeds.into());
    }

    // Create participation account
    let space = EpochParticipation::SIZE;
    let rent_lamports = pinocchio::sysvars::rent::Rent::get()?.minimum_balance(space);

    let bump_seed = [bump];
    let signer_seeds = [
        Seed::from(EpochParticipation::SEEDS_PREFIX),
        Seed::from(epoch_id_bytes.as_ref()),
        Seed::from(nft_asset.key().as_ref()),
        Seed::from(&bump_seed),
    ];
    let signer = Signer::from(&signer_seeds);

    pinocchio_system::instructions::CreateAccount {
        from: owner,
        to: participation_account,
        lamports: rent_lamports,
        space: space as u64,
        owner: program_id,
    }
    .invoke_signed(&[signer])?;

    // Initialize participation data
    let participation_data = unsafe { participation_account.borrow_mut_data_unchecked() };

    // discriminator
    participation_data[0..8].copy_from_slice(&EpochParticipation::DISCRIMINATOR);
    // epoch_id
    participation_data[8..16].copy_from_slice(&epoch_id.to_le_bytes());
    // nft_mint
    participation_data[16..48].copy_from_slice(nft_asset.key().as_ref());
    // owner_at_join
    participation_data[48..80].copy_from_slice(owner.key().as_ref());
    // hashrate_at_join
    participation_data[80..88].copy_from_slice(&hashrate.to_le_bytes());
    // joined_at
    participation_data[88..96].copy_from_slice(&now.to_le_bytes());
    // effective_hashrate
    participation_data[96..104].copy_from_slice(&effective_hashrate.to_le_bytes());
    // weighted_hashrate (will be set when rent is paid, initially same as effective)
    participation_data[104..112].copy_from_slice(&effective_hashrate.to_le_bytes());
    // rent_paid = false initially
    participation_data[112] = 0;
    // hashrate_claimed = false
    participation_data[113] = 0;
    // ticket_claimed = false
    participation_data[114] = 0;
    // bump
    participation_data[115] = bump;
    // won_hashrate_pool = false (set by finalize_epoch if winner)
    participation_data[116] = 0;
    // won_ticket_pool = false (set by finalize_epoch if winner)
    participation_data[117] = 0;
    // padding
    participation_data[118..120].copy_from_slice(&[0u8; 2]);

    // Update epoch counters
    let current_total_hashrate = u64::from_le_bytes(
        epoch_data[40..48]
            .try_into()
            .map_err(|_| MiningError::InvalidAccountData)?,
    );
    let current_participants = u32::from_le_bytes(
        epoch_data[48..52]
            .try_into()
            .map_err(|_| MiningError::InvalidAccountData)?,
    );

    let new_total_hashrate = current_total_hashrate.saturating_add(effective_hashrate);
    let new_participants = current_participants.saturating_add(1);

    epoch_data[40..48].copy_from_slice(&new_total_hashrate.to_le_bytes());
    epoch_data[48..52].copy_from_slice(&new_participants.to_le_bytes());

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_effectiveness_calculation() {
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
}
