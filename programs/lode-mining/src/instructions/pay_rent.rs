//! Pay rent instruction
//!
//! Pays LODE rent for an NFT to participate in epoch lottery.
//! Rent = base_rent + (hashrate * hashrate_rent_bps / 10000)
//! 70% burned, 30% to lottery pool.
//!
//! Accounts:
//! 0. [signer] Owner/authority
//! 1. [] MiningConfig PDA
//! 2. [] Epoch PDA
//! 3. [writable] EpochParticipation PDA
//! 4. [] NFT asset account
//! 5. [writable] LODE mint
//! 6. [writable] Owner's LODE token account
//! 7. [writable] Lottery pool token account
//! 8. [] Token-2022 program

use crate::{
    error::MiningError,
    mpl_core::parse_miner_attributes,
    state::{Epoch, EpochParticipation, MiningConfig},
};
use pinocchio::{
    account_info::AccountInfo,
    program_error::ProgramError,
    pubkey::Pubkey,
    sysvars::{clock::Clock, Sysvar},
    ProgramResult,
};

/// Calculate rent for an NFT miner
pub fn calculate_rent(base_rent: u64, hashrate: u64, hashrate_rent_bps: u16) -> u64 {
    let hashrate_rent = hashrate
        .checked_mul(hashrate_rent_bps as u64)
        .unwrap_or(0)
        / 10000;
    base_rent.saturating_add(hashrate_rent)
}

/// Process pay_rent instruction
pub fn process(_program_id: &Pubkey, accounts: &[AccountInfo], _data: &[u8]) -> ProgramResult {
    let [owner, config_account, epoch_account, participation_account, nft_asset, lode_mint, owner_token_account, lottery_pool, _token_program] =
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

    // Validate config account
    let config_data = unsafe { config_account.borrow_data_unchecked() };
    if config_data.len() < MiningConfig::SIZE {
        return Err(MiningError::InvalidAccountData.into());
    }
    if config_data[0..8] != MiningConfig::DISCRIMINATOR {
        return Err(MiningError::InvalidPdaSeeds.into());
    }

    // Parse config
    let base_rent = u64::from_le_bytes(
        config_data[48..56]
            .try_into()
            .map_err(|_| MiningError::InvalidAccountData)?,
    );
    let hashrate_rent_bps = u16::from_le_bytes(
        config_data[56..58]
            .try_into()
            .map_err(|_| MiningError::InvalidAccountData)?,
    );
    let grace_period_pct = config_data[58];
    let epoch_duration = u64::from_le_bytes(
        config_data[24..32]
            .try_into()
            .map_err(|_| MiningError::InvalidAccountData)?,
    );

    // Validate epoch account
    let epoch_data = unsafe { epoch_account.borrow_data_unchecked() };
    if epoch_data.len() < Epoch::SIZE {
        return Err(MiningError::InvalidAccountData.into());
    }
    if epoch_data[0..8] != Epoch::DISCRIMINATOR {
        return Err(MiningError::InvalidPdaSeeds.into());
    }

    // Check epoch is active
    let epoch_state = epoch_data[57];
    if epoch_state != Epoch::STATE_ACTIVE {
        return Err(MiningError::EpochNotActive.into());
    }

    // Check within grace period
    let start_timestamp = i64::from_le_bytes(
        epoch_data[16..24]
            .try_into()
            .map_err(|_| MiningError::InvalidAccountData)?,
    );

    let clock = Clock::get()?;
    let elapsed = clock.unix_timestamp.saturating_sub(start_timestamp) as u64;
    let grace_duration = epoch_duration * (grace_period_pct as u64) / 100;

    if elapsed > grace_duration {
        return Err(MiningError::GracePeriodExpired.into());
    }

    // Validate participation account
    let participation_data = unsafe { participation_account.borrow_mut_data_unchecked() };
    if participation_data.len() < EpochParticipation::SIZE {
        return Err(MiningError::InvalidAccountData.into());
    }
    if participation_data[0..8] != EpochParticipation::DISCRIMINATOR {
        return Err(MiningError::InvalidPdaSeeds.into());
    }

    // Check rent not already paid
    if participation_data[104] != 0 {
        return Err(MiningError::RentAlreadyPaid.into());
    }

    // Get hashrate from NFT
    let nft_data = unsafe { nft_asset.borrow_data_unchecked() };
    let (hashrate, _, _, _) =
        parse_miner_attributes(&nft_data).ok_or(MiningError::InvalidAccountData)?;

    // Calculate rent
    let rent = calculate_rent(base_rent, hashrate, hashrate_rent_bps);
    let burn_amount = rent * 70 / 100;
    let lottery_amount = rent - burn_amount;

    // Step 1: Burn 70% of rent
    pinocchio_token::instructions::Burn {
        account: owner_token_account,
        mint: lode_mint,
        authority: owner,
        amount: burn_amount,
    }
    .invoke()?;

    // Step 2: Transfer 30% to lottery pool
    pinocchio_token::instructions::Transfer {
        from: owner_token_account,
        to: lottery_pool,
        authority: owner,
        amount: lottery_amount,
    }
    .invoke()?;

    // Step 3: Mark rent as paid
    participation_data[104] = 1; // rent_paid = true

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rent_calculation() {
        // Base rent only (no hashrate)
        let rent = calculate_rent(1_000_000_000, 0, 1);
        assert_eq!(rent, 1_000_000_000);

        // With hashrate: base + 0.01% of 1M = 1B + 100
        let rent = calculate_rent(1_000_000_000, 1_000_000, 1);
        assert_eq!(rent, 1_000_000_100);

        // Higher hashrate: base + 0.01% of 100M = 1B + 10000
        let rent = calculate_rent(1_000_000_000, 100_000_000, 1);
        assert_eq!(rent, 1_000_010_000);
    }
}
