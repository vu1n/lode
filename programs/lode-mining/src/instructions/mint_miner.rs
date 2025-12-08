//! Mint miner instruction
//!
//! Burns LODE and mints a new NFT miner with initial hashrate.
//! 70% of LODE burned, 30% to lottery pool.
//!
//! Accounts:
//! 0. [signer] Payer/authority
//! 1. [] MiningConfig PDA
//! 2. [writable] LODE mint
//! 3. [writable] Payer's LODE token account
//! 4. [signer, writable] New NFT asset keypair
//! 5. [writable] Lottery pool token account
//! 6. [] Token-2022 program
//! 7. [] MPL Core program
//! 8. [] System program

use crate::{error::MiningError, mpl_core::CreateV1, state::MiningConfig};
use pinocchio::{
    account_info::AccountInfo, program_error::ProgramError, pubkey::Pubkey, ProgramResult,
};

/// Mint amount calculation
pub struct MintCost {
    pub total: u64,
    pub burn_amount: u64,
    pub lottery_amount: u64,
}

impl MintCost {
    /// Calculate mint cost with progressive fee
    /// Base cost increases by 50% as epoch progresses
    pub fn calculate(base_mint_cost: u64, epoch_progress_bps: u16) -> Self {
        // Progressive multiplier: 1.0 at start, 1.5 at end
        let multiplier = 10000u64 + (epoch_progress_bps as u64 / 2);
        let total = base_mint_cost
            .checked_mul(multiplier)
            .unwrap_or(base_mint_cost)
            / 10000;

        // 70% burn, 30% lottery
        let burn_amount = total * 70 / 100;
        let lottery_amount = total - burn_amount;

        Self {
            total,
            burn_amount,
            lottery_amount,
        }
    }
}

/// Process mint_miner instruction
///
/// Instruction data format:
/// - [0..32] NFT name (null-terminated or full 32 bytes)
/// - [32..64] NFT URI prefix (we append miner number)
/// - [64..72] Initial hashrate (u64 little-endian)
/// - [72..74] Epoch progress in basis points (for progressive fee)
pub fn process(_program_id: &Pubkey, accounts: &[AccountInfo], data: &[u8]) -> ProgramResult {
    let [payer, config_account, lode_mint, payer_token_account, nft_asset, lottery_pool, _token_program, mpl_core_program, system_program] =
        accounts
    else {
        return Err(ProgramError::NotEnoughAccountKeys);
    };

    // Validate payer is signer
    if !payer.is_signer() {
        return Err(MiningError::AccountNotSigner.into());
    }

    // Validate NFT asset is signer (new keypair)
    if !nft_asset.is_signer() {
        return Err(MiningError::AccountNotSigner.into());
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
    let base_mint_cost = u64::from_le_bytes(
        config_data[56..64]
            .try_into()
            .map_err(|_| MiningError::InvalidAccountData)?,
    );
    let current_epoch = u64::from_le_bytes(
        config_data[40..48]
            .try_into()
            .map_err(|_| MiningError::InvalidAccountData)?,
    );

    // Parse instruction data
    if data.len() < 74 {
        return Err(ProgramError::InvalidInstructionData);
    }

    // Extract name (find null terminator or use full 32 bytes)
    let name_bytes = &data[0..32];
    let name_len = name_bytes.iter().position(|&b| b == 0).unwrap_or(32);
    let name = core::str::from_utf8(&name_bytes[..name_len])
        .map_err(|_| ProgramError::InvalidInstructionData)?;

    // Extract URI
    let uri_bytes = &data[32..64];
    let uri_len = uri_bytes.iter().position(|&b| b == 0).unwrap_or(32);
    let uri = core::str::from_utf8(&uri_bytes[..uri_len])
        .map_err(|_| ProgramError::InvalidInstructionData)?;

    // Extract hashrate
    let hashrate = u64::from_le_bytes(
        data[64..72]
            .try_into()
            .map_err(|_| ProgramError::InvalidInstructionData)?,
    );

    // Extract epoch progress (basis points)
    let epoch_progress_bps = u16::from_le_bytes(
        data[72..74]
            .try_into()
            .map_err(|_| ProgramError::InvalidInstructionData)?,
    );

    // Calculate mint cost with progressive fee
    let cost = MintCost::calculate(base_mint_cost, epoch_progress_bps);

    // Step 1: Burn 70% of LODE payment
    pinocchio_token::instructions::Burn {
        account: payer_token_account,
        mint: lode_mint,
        authority: payer,
        amount: cost.burn_amount,
    }
    .invoke()?;

    // Step 2: Transfer 30% to lottery pool
    pinocchio_token::instructions::Transfer {
        from: payer_token_account,
        to: lottery_pool,
        authority: payer,
        amount: cost.lottery_amount,
    }
    .invoke()?;

    // Step 3: Create NFT via Metaplex Core
    CreateV1 {
        asset: nft_asset,
        payer,
        owner: Some(payer),
        update_authority: Some(config_account), // Config PDA as update authority
        system_program,
        mpl_core_program,
        name,
        uri,
        hashrate,
        created_epoch: current_epoch,
    }
    .invoke()?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mint_cost_calculation() {
        // At epoch start (0 bps), no progressive fee
        let cost = MintCost::calculate(100_000_000_000, 0);
        assert_eq!(cost.total, 100_000_000_000);
        assert_eq!(cost.burn_amount, 70_000_000_000);
        assert_eq!(cost.lottery_amount, 30_000_000_000);

        // At epoch mid (5000 bps = 50%), 25% fee increase
        let cost = MintCost::calculate(100_000_000_000, 5000);
        assert_eq!(cost.total, 125_000_000_000);
        assert_eq!(cost.burn_amount, 87_500_000_000);
        assert_eq!(cost.lottery_amount, 37_500_000_000);

        // At epoch end (10000 bps = 100%), 50% fee increase
        let cost = MintCost::calculate(100_000_000_000, 10000);
        assert_eq!(cost.total, 150_000_000_000);
        assert_eq!(cost.burn_amount, 105_000_000_000);
        assert_eq!(cost.lottery_amount, 45_000_000_000);
    }
}
