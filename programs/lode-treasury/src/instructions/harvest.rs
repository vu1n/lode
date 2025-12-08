//! Harvest instruction
//!
//! Withdraws withheld transfer fees and distributes according to fee split:
//! - 30% burned
//! - 50% to lottery pool
//! - 20% to POL treasury
//!
//! Accounts:
//! 0. [signer] Authority
//! 1. [writable] Treasury PDA
//! 2. [writable] LODE mint (for burning)
//! 3. [writable] Fee source account (withheld fees)
//! 4. [writable] Lottery pool account
//! 5. [writable] POL treasury account
//! 6. [] Token-2022 program

use crate::{error::TreasuryError, state::Treasury};
use pinocchio::{
    account_info::AccountInfo, program_error::ProgramError, pubkey::Pubkey, ProgramResult,
};

/// Process harvest instruction
pub fn process(_program_id: &Pubkey, accounts: &[AccountInfo], _data: &[u8]) -> ProgramResult {
    let [authority, treasury_account, _mint, _fee_source, _lottery_pool, _pol_account, _token_program] =
        accounts
    else {
        return Err(ProgramError::NotEnoughAccountKeys);
    };

    // Validate authority is signer
    if !authority.is_signer() {
        return Err(TreasuryError::AccountNotSigner.into());
    }

    // Validate treasury account
    if !treasury_account.is_writable() {
        return Err(TreasuryError::AccountNotWritable.into());
    }

    let treasury_data = unsafe { treasury_account.borrow_data_unchecked() };

    // Validate discriminator
    if treasury_data[0..8] != Treasury::DISCRIMINATOR {
        return Err(TreasuryError::InvalidPdaSeeds.into());
    }

    // Validate authority matches
    if &treasury_data[8..40] != authority.key().as_ref() {
        return Err(TreasuryError::InvalidAuthority.into());
    }

    // TODO: Implement Token-2022 withheld fee harvesting via CPI
    // This requires:
    // 1. Calling Token-2022's HarvestWithheldTokensToMint or WithdrawWithheldTokensFromAccounts
    // 2. Reading the amount harvested
    // 3. Distributing according to burn_bps/lottery_bps/treasury_bps
    // 4. Updating total_burned, total_to_lottery, total_to_pol counters

    // For now, this is a placeholder. Full Token-2022 CPI will be added when
    // we have the mint account properly set up with TransferFeeConfig extension.

    Ok(())
}
