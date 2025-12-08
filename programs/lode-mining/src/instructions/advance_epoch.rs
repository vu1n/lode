//! Advance epoch instruction
//!
//! Transitions from current epoch to next epoch.
//! Can be called by anyone (permissionless crank).
//! Handles rollover from previous epoch if there were no winners.
//!
//! Accounts:
//! 0. [signer] Payer
//! 1. [writable] MiningConfig PDA
//! 2. [writable] Current Epoch PDA
//! 3. [writable] Next Epoch PDA (to be created)
//! 4. [] System program

use crate::{
    error::MiningError,
    state::{Epoch, MiningConfig},
};
use pinocchio::{
    account_info::AccountInfo,
    instruction::{Seed, Signer},
    program_error::ProgramError,
    pubkey::{find_program_address, Pubkey},
    sysvars::{clock::Clock, Sysvar},
    ProgramResult,
};

/// Process advance_epoch instruction
pub fn process(program_id: &Pubkey, accounts: &[AccountInfo], _data: &[u8]) -> ProgramResult {
    let [payer, config_account, current_epoch_account, next_epoch_account, _system_program] =
        accounts
    else {
        return Err(ProgramError::NotEnoughAccountKeys);
    };

    // Validate payer is signer
    if !payer.is_signer() {
        return Err(MiningError::AccountNotSigner.into());
    }

    // Validate config is writable
    if !config_account.is_writable() {
        return Err(MiningError::AccountNotWritable.into());
    }

    // Validate current epoch is writable
    if !current_epoch_account.is_writable() {
        return Err(MiningError::AccountNotWritable.into());
    }

    // Validate next epoch is writable
    if !next_epoch_account.is_writable() {
        return Err(MiningError::AccountNotWritable.into());
    }

    // Validate and read config
    let config_data = unsafe { config_account.borrow_mut_data_unchecked() };
    if config_data.len() < MiningConfig::SIZE {
        return Err(MiningError::InvalidAccountData.into());
    }
    if config_data[0..8] != MiningConfig::DISCRIMINATOR {
        return Err(MiningError::InvalidPdaSeeds.into());
    }

    let current_epoch_id = u64::from_le_bytes(
        config_data[40..48]
            .try_into()
            .map_err(|_| MiningError::InvalidAccountData)?,
    );
    let epoch_duration = u64::from_le_bytes(
        config_data[48..56]
            .try_into()
            .map_err(|_| MiningError::InvalidAccountData)?,
    );

    // Validate current epoch account
    let current_epoch_data = unsafe { current_epoch_account.borrow_mut_data_unchecked() };
    if current_epoch_data.len() < Epoch::SIZE {
        return Err(MiningError::InvalidAccountData.into());
    }
    if current_epoch_data[0..8] != Epoch::DISCRIMINATOR {
        return Err(MiningError::InvalidPdaSeeds.into());
    }

    // Check current epoch is finalized
    let current_epoch_state = current_epoch_data[60];
    if current_epoch_state != Epoch::STATE_FINALIZED {
        return Err(MiningError::EpochNotFinalized.into());
    }

    let current_end_timestamp = i64::from_le_bytes(
        current_epoch_data[24..32]
            .try_into()
            .map_err(|_| MiningError::InvalidAccountData)?,
    );

    // Get rollover amount from current epoch (bytes 56-64)
    let rollover_amount = u64::from_le_bytes(
        current_epoch_data[56..64]
            .try_into()
            .map_err(|_| MiningError::InvalidAccountData)?,
    );

    // Get current time
    let clock = Clock::get()?;
    let now = clock.unix_timestamp;

    // Check epoch has actually ended
    if now < current_end_timestamp {
        return Err(MiningError::EpochNotActive.into());
    }

    // Calculate next epoch parameters
    let next_epoch_id = current_epoch_id.saturating_add(1);
    let next_start = current_end_timestamp;
    let next_end = next_start.saturating_add(epoch_duration as i64);

    // Derive next epoch PDA
    let next_epoch_id_bytes = next_epoch_id.to_le_bytes();
    let seeds = &[Epoch::SEEDS_PREFIX, &next_epoch_id_bytes];
    let (expected_pda, bump) = find_program_address(seeds, program_id);

    if next_epoch_account.key() != &expected_pda {
        return Err(MiningError::InvalidPdaSeeds.into());
    }

    // Create next epoch account
    let space = Epoch::SIZE;
    let rent_lamports = pinocchio::sysvars::rent::Rent::get()?.minimum_balance(space);

    let bump_seed = [bump];
    let signer_seeds = [
        Seed::from(Epoch::SEEDS_PREFIX),
        Seed::from(next_epoch_id_bytes.as_ref()),
        Seed::from(&bump_seed),
    ];
    let signer = Signer::from(&signer_seeds);

    pinocchio_system::instructions::CreateAccount {
        from: payer,
        to: next_epoch_account,
        lamports: rent_lamports,
        space: space as u64,
        owner: program_id,
    }
    .invoke_signed(&[signer])?;

    // Initialize next epoch data with rollover included
    let next_epoch_data = unsafe { next_epoch_account.borrow_mut_data_unchecked() };

    // Split rollover 80/20 like regular pools
    let rollover_hashrate = (rollover_amount * 8000) / 10000; // 80%
    let rollover_ticket = rollover_amount.saturating_sub(rollover_hashrate); // 20%

    // discriminator (bytes 0-8)
    next_epoch_data[0..8].copy_from_slice(&Epoch::DISCRIMINATOR);
    // epoch_id (bytes 8-16)
    next_epoch_data[8..16].copy_from_slice(&next_epoch_id.to_le_bytes());
    // start_timestamp (bytes 16-24)
    next_epoch_data[16..24].copy_from_slice(&next_start.to_le_bytes());
    // end_timestamp (bytes 24-32)
    next_epoch_data[24..32].copy_from_slice(&next_end.to_le_bytes());
    // hashrate_pool = rollover_hashrate (bytes 32-40)
    next_epoch_data[32..40].copy_from_slice(&rollover_hashrate.to_le_bytes());
    // ticket_pool = rollover_ticket (bytes 40-48)
    next_epoch_data[40..48].copy_from_slice(&rollover_ticket.to_le_bytes());
    // total_hashrate = 0 (bytes 48-56)
    next_epoch_data[48..56].copy_from_slice(&0u64.to_le_bytes());
    // rollover_amount = 0 (bytes 56-64) - starts fresh
    next_epoch_data[56..64].copy_from_slice(&0u64.to_le_bytes());
    // total_participants = 0 (bytes 64-68)
    next_epoch_data[64..68].copy_from_slice(&0u32.to_le_bytes());
    // state = active (byte 60)
    next_epoch_data[60] = Epoch::STATE_ACTIVE;
    // bump (byte 61)
    next_epoch_data[61] = bump;
    // vrf_seed = 0 (bytes 62-70)
    next_epoch_data[62..70].copy_from_slice(&0u64.to_le_bytes());
    // total_weighted_hashrate = 0 (bytes 70-78)
    next_epoch_data[70..78].copy_from_slice(&0u64.to_le_bytes());
    // difficulty = default (bytes 78-86)
    next_epoch_data[78..86].copy_from_slice(&Epoch::DEFAULT_DIFFICULTY.to_le_bytes());
    // hashrate_winner_count = 0 (bytes 86-88)
    next_epoch_data[86..88].copy_from_slice(&0u16.to_le_bytes());
    // ticket_winner_count = 0 (bytes 88-90)
    next_epoch_data[88..90].copy_from_slice(&0u16.to_le_bytes());
    // padding (bytes 90-104)
    next_epoch_data[90..104].copy_from_slice(&[0u8; 14]);

    // Update config with new current epoch
    config_data[40..48].copy_from_slice(&next_epoch_id.to_le_bytes());

    Ok(())
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_epoch_advance_logic() {
        // Epoch duration is 24 hours (86400 seconds)
        let duration = 86400u64;
        let start = 1000000i64;
        let end = start + duration as i64;

        assert_eq!(end, 1086400);

        // Next epoch starts where previous ended
        let next_start = end;
        let next_end = next_start + duration as i64;
        assert_eq!(next_start, 1086400);
        assert_eq!(next_end, 1172800);
    }

    #[test]
    fn test_rollover_splitting() {
        let rollover = 100_000_000_000u64; // 100 LODE

        // 80/20 split
        let rollover_hashrate = (rollover * 8000) / 10000;
        let rollover_ticket = rollover - rollover_hashrate;

        assert_eq!(rollover_hashrate, 80_000_000_000);
        assert_eq!(rollover_ticket, 20_000_000_000);
    }

    #[test]
    fn test_no_rollover() {
        let rollover = 0u64; // No rollover (all prizes claimed)

        let rollover_hashrate = (rollover * 8000) / 10000;
        let rollover_ticket = rollover - rollover_hashrate;

        assert_eq!(rollover_hashrate, 0);
        assert_eq!(rollover_ticket, 0);
    }
}
