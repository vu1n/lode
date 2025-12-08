//! Initialize instruction
//!
//! Creates the MiningConfig PDA with epoch and rent parameters.

use crate::{error::MiningError, state::MiningConfig, ID};
use pinocchio::{
    account_info::AccountInfo,
    instruction::{Seed, Signer},
    program_error::ProgramError,
    pubkey::{find_program_address, Pubkey},
    sysvars::{clock::Clock, rent::Rent, Sysvar},
    ProgramResult,
};

pub fn process(_program_id: &Pubkey, accounts: &[AccountInfo], _data: &[u8]) -> ProgramResult {
    let [authority, config_account, _system_program] = accounts else {
        return Err(ProgramError::NotEnoughAccountKeys);
    };

    if !authority.is_signer() {
        return Err(MiningError::AccountNotSigner.into());
    }

    let (expected_config, bump) = find_program_address(&[MiningConfig::SEEDS], &ID);
    if config_account.key() != &expected_config {
        return Err(MiningError::InvalidPdaSeeds.into());
    }

    if !config_account.data_is_empty() {
        return Err(MiningError::AlreadyInitialized.into());
    }

    if !config_account.is_writable() {
        return Err(MiningError::AccountNotWritable.into());
    }

    let rent = Rent::get()?;
    let config_rent = rent.minimum_balance(MiningConfig::SIZE);

    let bump_seed = [bump];
    let signer_seeds = [Seed::from(MiningConfig::SEEDS), Seed::from(&bump_seed)];
    let signer = Signer::from(&signer_seeds);

    pinocchio_system::instructions::CreateAccount {
        from: authority,
        to: config_account,
        lamports: config_rent,
        space: MiningConfig::SIZE as u64,
        owner: &ID,
    }
    .invoke_signed(&[signer])?;

    let clock = Clock::get()?;
    let config_data = unsafe { config_account.borrow_mut_data_unchecked() };

    config_data[0..8].copy_from_slice(&MiningConfig::DISCRIMINATOR);
    config_data[8..40].copy_from_slice(authority.key().as_ref());
    config_data[40..48].copy_from_slice(&0u64.to_le_bytes()); // current_epoch
    config_data[48..56].copy_from_slice(&MiningConfig::DEFAULT_EPOCH_DURATION.to_le_bytes());
    config_data[56..64].copy_from_slice(&MiningConfig::DEFAULT_BASE_RENT.to_le_bytes());
    config_data[64..66].copy_from_slice(&MiningConfig::DEFAULT_HASHRATE_RENT_BPS.to_le_bytes());
    config_data[66] = MiningConfig::DEFAULT_GRACE_PERIOD_PCT;
    config_data[67..69].copy_from_slice(&MiningConfig::DEFAULT_AGE_BONUS_BPS.to_le_bytes());
    config_data[69..71].copy_from_slice(&MiningConfig::DEFAULT_MAX_AGE_BONUS_BPS.to_le_bytes());
    config_data[71..79].copy_from_slice(&MiningConfig::DEFAULT_BASE_MINT_COST.to_le_bytes());
    config_data[79..87].copy_from_slice(&clock.unix_timestamp.to_le_bytes());
    config_data[87] = bump;

    Ok(())
}
