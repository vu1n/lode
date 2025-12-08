//! Upgrade miner instruction
//!
//! Burns LODE to increase an existing miner's hashrate.
//! 70% of LODE burned, 30% to lottery pool.
//!
//! Accounts:
//! 0. [signer] Owner/authority
//! 1. [] MiningConfig PDA
//! 2. [writable] LODE mint
//! 3. [writable] Owner's LODE token account
//! 4. [writable] NFT asset account
//! 5. [writable] Lottery pool token account
//! 6. [] Token-2022 program
//! 7. [] MPL Core program
//! 8. [] System program

use crate::{
    error::MiningError,
    mpl_core::{parse_miner_attributes, UpdateAttributesV1},
    state::MiningConfig,
};
use pinocchio::{
    account_info::AccountInfo, program_error::ProgramError, pubkey::Pubkey, ProgramResult,
};

/// Process upgrade_miner instruction
///
/// Instruction data format:
/// - [0..8] Additional hashrate to add (u64 little-endian)
/// - [8..16] LODE amount to spend (u64 little-endian)
pub fn process(_program_id: &Pubkey, accounts: &[AccountInfo], data: &[u8]) -> ProgramResult {
    let [owner, config_account, lode_mint, owner_token_account, nft_asset, lottery_pool, _token_program, mpl_core_program, system_program] =
        accounts
    else {
        return Err(ProgramError::NotEnoughAccountKeys);
    };

    // Validate owner is signer
    if !owner.is_signer() {
        return Err(MiningError::AccountNotSigner.into());
    }

    // Validate NFT asset is writable
    if !nft_asset.is_writable() {
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

    // Parse current epoch from config
    let current_epoch = u64::from_le_bytes(
        config_data[40..48]
            .try_into()
            .map_err(|_| MiningError::InvalidAccountData)?,
    );

    // Parse instruction data
    if data.len() < 16 {
        return Err(ProgramError::InvalidInstructionData);
    }

    let additional_hashrate = u64::from_le_bytes(
        data[0..8]
            .try_into()
            .map_err(|_| ProgramError::InvalidInstructionData)?,
    );

    let lode_amount = u64::from_le_bytes(
        data[8..16]
            .try_into()
            .map_err(|_| ProgramError::InvalidInstructionData)?,
    );

    // Get current NFT attributes
    let nft_data = unsafe { nft_asset.borrow_data_unchecked() };
    let (current_hashrate, current_burned, created_epoch, _) =
        parse_miner_attributes(&nft_data).ok_or(MiningError::InvalidAccountData)?;

    // Calculate burn/lottery split (70/30)
    let burn_amount = lode_amount * 70 / 100;
    let lottery_amount = lode_amount - burn_amount;

    // Step 1: Burn 70% of LODE payment
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

    // Step 3: Update NFT attributes with new hashrate
    let new_hashrate = current_hashrate.saturating_add(additional_hashrate);
    let new_total_burned = current_burned.saturating_add(burn_amount);

    UpdateAttributesV1 {
        asset: nft_asset,
        payer: owner,
        authority: owner,
        system_program,
        mpl_core_program,
        hashrate: new_hashrate,
        total_burned: new_total_burned,
        created_epoch,
        last_upgraded_epoch: current_epoch,
    }
    .invoke()?;

    Ok(())
}
