//! Initialize instruction
//!
//! Creates the Token-2022 mint with TransferFee extension and initializes
//! the TokenConfig PDA.
//!
//! Accounts:
//! 0. [signer] Authority (payer)
//! 1. [writable] TokenConfig PDA
//! 2. [writable] Mint account (Token-2022)
//! 3. [] System program
//! 4. [] Token-2022 program

use crate::{error::TokenError, state::TokenConfig, ID};
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
/// - transfer_fee_bps: u16 (optional, defaults to 50)
pub fn process(_program_id: &Pubkey, accounts: &[AccountInfo], data: &[u8]) -> ProgramResult {
    // Parse accounts
    let [authority, config_account, mint_account, _system_program, _token_program] = accounts
    else {
        return Err(ProgramError::NotEnoughAccountKeys);
    };

    // Validate authority is signer
    if !authority.is_signer() {
        return Err(TokenError::AccountNotSigner.into());
    }

    // Parse optional transfer fee from instruction data
    let transfer_fee_bps = if data.len() >= 2 {
        u16::from_le_bytes([data[0], data[1]])
    } else {
        TokenConfig::DEFAULT_TRANSFER_FEE_BPS
    };

    // Validate transfer fee
    if transfer_fee_bps > TokenConfig::MAX_FEE_BPS {
        return Err(TokenError::InvalidTransferFeeBps.into());
    }

    // Derive and validate config PDA
    let (expected_config, bump) = find_program_address(&[TokenConfig::SEEDS], &ID);
    if config_account.key() != &expected_config {
        return Err(TokenError::InvalidPdaSeeds.into());
    }

    // Check config not already initialized
    if !config_account.data_is_empty() {
        return Err(TokenError::AlreadyInitialized.into());
    }

    // Validate config account is writable
    if !config_account.is_writable() {
        return Err(TokenError::AccountNotWritable.into());
    }

    // Calculate rent for config account
    let rent = Rent::get()?;
    let config_rent = rent.minimum_balance(TokenConfig::SIZE);

    // Create config PDA
    let bump_seed = [bump];
    let signer_seeds = [Seed::from(TokenConfig::SEEDS), Seed::from(&bump_seed)];
    let signer = Signer::from(&signer_seeds);

    pinocchio_system::instructions::CreateAccount {
        from: authority,
        to: config_account,
        lamports: config_rent,
        space: TokenConfig::SIZE as u64,
        owner: &ID,
    }
    .invoke_signed(&[signer])?;

    // Initialize config data
    let config_data = unsafe { config_account.borrow_mut_data_unchecked() };

    // Write discriminator
    config_data[0..8].copy_from_slice(&TokenConfig::DISCRIMINATOR);

    // Write mint pubkey
    config_data[8..40].copy_from_slice(mint_account.key().as_ref());

    // Write authority pubkey
    config_data[40..72].copy_from_slice(authority.key().as_ref());

    // Write max supply (little-endian)
    config_data[72..80].copy_from_slice(&TokenConfig::MAX_SUPPLY.to_le_bytes());

    // Write transfer fee bps (little-endian)
    config_data[80..82].copy_from_slice(&transfer_fee_bps.to_le_bytes());

    // Write bump
    config_data[82] = bump;

    // Initialize Token-2022 mint with TransferFee extension
    // The mint account should already be created by the caller with enough space
    // for the TransferFee extension. We just initialize it here.

    // Note: Token-2022 mint initialization with extensions requires:
    // 1. Account created with space for Mint + TransferFeeConfig extension
    // 2. InitializeMint2 instruction
    // 3. Initialize TransferFeeConfig extension
    //
    // For now, we assume the mint is pre-created. Full Token-2022 CPI
    // will be added in a follow-up task.

    Ok(())
}
