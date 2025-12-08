//! Initialize instruction
//!
//! Creates the Treasury PDA with fee distribution configuration.
//!
//! Accounts:
//! 0. [signer] Authority (payer)
//! 1. [writable] Treasury PDA
//! 2. [] LODE token mint
//! 3. [] System program

use crate::{error::TreasuryError, state::Treasury, ID};
use pinocchio::{
    account_info::AccountInfo,
    instruction::{Seed, Signer},
    program_error::ProgramError,
    pubkey::{find_program_address, Pubkey},
    sysvars::{rent::Rent, Sysvar},
    ProgramResult,
};

/// Process initialize instruction
///
/// Instruction data:
/// - burn_bps: u16 (optional, defaults to 3000)
/// - lottery_bps: u16 (optional, defaults to 5000)
/// - treasury_bps: u16 (optional, defaults to 2000)
pub fn process(_program_id: &Pubkey, accounts: &[AccountInfo], data: &[u8]) -> ProgramResult {
    let [authority, treasury_account, mint_account, _system_program] = accounts else {
        return Err(ProgramError::NotEnoughAccountKeys);
    };

    // Validate authority is signer
    if !authority.is_signer() {
        return Err(TreasuryError::AccountNotSigner.into());
    }

    // Parse optional fee split from instruction data
    let (burn_bps, lottery_bps, treasury_bps) = if data.len() >= 6 {
        let burn = u16::from_le_bytes([data[0], data[1]]);
        let lottery = u16::from_le_bytes([data[2], data[3]]);
        let treasury = u16::from_le_bytes([data[4], data[5]]);
        (burn, lottery, treasury)
    } else {
        (
            Treasury::DEFAULT_BURN_BPS,
            Treasury::DEFAULT_LOTTERY_BPS,
            Treasury::DEFAULT_TREASURY_BPS,
        )
    };

    // Validate fee split
    if !Treasury::validate_fee_split(burn_bps, lottery_bps, treasury_bps) {
        return Err(TreasuryError::InvalidFeeSplit.into());
    }

    // Derive and validate treasury PDA
    let (expected_treasury, bump) = find_program_address(&[Treasury::SEEDS], &ID);
    if treasury_account.key() != &expected_treasury {
        return Err(TreasuryError::InvalidPdaSeeds.into());
    }

    // Check treasury not already initialized
    if !treasury_account.data_is_empty() {
        return Err(TreasuryError::AlreadyInitialized.into());
    }

    // Validate treasury account is writable
    if !treasury_account.is_writable() {
        return Err(TreasuryError::AccountNotWritable.into());
    }

    // Calculate rent
    let rent = Rent::get()?;
    let treasury_rent = rent.minimum_balance(Treasury::SIZE);

    // Create treasury PDA
    let bump_seed = [bump];
    let signer_seeds = [Seed::from(Treasury::SEEDS), Seed::from(&bump_seed)];
    let signer = Signer::from(&signer_seeds);

    pinocchio_system::instructions::CreateAccount {
        from: authority,
        to: treasury_account,
        lamports: treasury_rent,
        space: Treasury::SIZE as u64,
        owner: &ID,
    }
    .invoke_signed(&[signer])?;

    // Initialize treasury data
    let treasury_data = unsafe { treasury_account.borrow_mut_data_unchecked() };

    // Write discriminator
    treasury_data[0..8].copy_from_slice(&Treasury::DISCRIMINATOR);

    // Write authority pubkey
    treasury_data[8..40].copy_from_slice(authority.key().as_ref());

    // Write mint pubkey
    treasury_data[40..72].copy_from_slice(mint_account.key().as_ref());

    // Write fee split
    treasury_data[72..74].copy_from_slice(&burn_bps.to_le_bytes());
    treasury_data[74..76].copy_from_slice(&lottery_bps.to_le_bytes());
    treasury_data[76..78].copy_from_slice(&treasury_bps.to_le_bytes());

    // Write zeroed counters (total_burned, total_to_lottery, total_to_pol)
    treasury_data[78..86].copy_from_slice(&0u64.to_le_bytes());
    treasury_data[86..94].copy_from_slice(&0u64.to_le_bytes());
    treasury_data[94..102].copy_from_slice(&0u64.to_le_bytes());

    // Write bump
    treasury_data[102] = bump;

    Ok(())
}
