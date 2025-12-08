//! Claim instruction
//!
//! Claims lottery winnings for a winning NFT.
//! With hash/mask mining, multiple winners can exist - prize is split equally.
//!
//! Accounts:
//! 0. [signer] Winner (current NFT owner)
//! 1. [] MiningConfig PDA
//! 2. [] Epoch PDA
//! 3. [writable] EpochParticipation PDA
//! 4. [] NFT asset account
//! 5. [writable] Winner's LODE token account
//! 6. [writable] Lottery pool token account
//! 7. [] Lottery pool authority PDA
//! 8. [] Token-2022 program

use crate::{
    error::MiningError,
    state::{Epoch, EpochParticipation, MiningConfig},
};
use pinocchio::{
    account_info::AccountInfo,
    instruction::{Seed, Signer},
    program_error::ProgramError,
    pubkey::{find_program_address, Pubkey},
    ProgramResult,
};

/// Lottery pool authority seeds
const LOTTERY_POOL_SEEDS: &[u8] = b"lottery_pool";

/// Process claim instruction
///
/// Instruction data:
/// - [0] claim_type: 0 = hashrate pool, 1 = ticket pool, 2 = both
pub fn process(program_id: &Pubkey, accounts: &[AccountInfo], data: &[u8]) -> ProgramResult {
    let [winner, config_account, epoch_account, participation_account, nft_asset, winner_token_account, lottery_pool, lottery_authority, _token_program] =
        accounts
    else {
        return Err(ProgramError::NotEnoughAccountKeys);
    };

    // Validate winner is signer
    if !winner.is_signer() {
        return Err(MiningError::AccountNotSigner.into());
    }

    // Validate participation is writable (to mark claimed)
    if !participation_account.is_writable() {
        return Err(MiningError::AccountNotWritable.into());
    }

    // Validate winner token account is writable
    if !winner_token_account.is_writable() {
        return Err(MiningError::AccountNotWritable.into());
    }

    // Validate lottery pool is writable
    if !lottery_pool.is_writable() {
        return Err(MiningError::AccountNotWritable.into());
    }

    // Parse claim type from instruction data
    let claim_type = if data.is_empty() { 2 } else { data[0] };

    // Validate config account
    let config_data = unsafe { config_account.borrow_data_unchecked() };
    if config_data.len() < MiningConfig::SIZE {
        return Err(MiningError::InvalidAccountData.into());
    }
    if config_data[0..8] != MiningConfig::DISCRIMINATOR {
        return Err(MiningError::InvalidPdaSeeds.into());
    }

    // Validate epoch account
    let epoch_data = unsafe { epoch_account.borrow_data_unchecked() };
    if epoch_data.len() < Epoch::SIZE {
        return Err(MiningError::InvalidAccountData.into());
    }
    if epoch_data[0..8] != Epoch::DISCRIMINATOR {
        return Err(MiningError::InvalidPdaSeeds.into());
    }

    // Check epoch is finalized
    let epoch_state = epoch_data[60];
    if epoch_state != Epoch::STATE_FINALIZED {
        return Err(MiningError::EpochNotFinalized.into());
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
    let ticket_pool_amount = u64::from_le_bytes(
        epoch_data[40..48]
            .try_into()
            .map_err(|_| MiningError::InvalidAccountData)?,
    );

    // Get winner counts for prize splitting
    let hashrate_winner_count = u16::from_le_bytes(
        epoch_data[86..88]
            .try_into()
            .map_err(|_| MiningError::InvalidAccountData)?,
    );
    let ticket_winner_count = u16::from_le_bytes(
        epoch_data[88..90]
            .try_into()
            .map_err(|_| MiningError::InvalidAccountData)?,
    );

    // Validate participation account
    let participation_data = unsafe { participation_account.borrow_mut_data_unchecked() };
    if participation_data.len() < EpochParticipation::SIZE {
        return Err(MiningError::InvalidAccountData.into());
    }
    if participation_data[0..8] != EpochParticipation::DISCRIMINATOR {
        return Err(MiningError::InvalidPdaSeeds.into());
    }

    // Verify epoch matches
    let part_epoch_id = u64::from_le_bytes(
        participation_data[8..16]
            .try_into()
            .map_err(|_| MiningError::InvalidAccountData)?,
    );
    if part_epoch_id != epoch_id {
        return Err(MiningError::InvalidAccountData.into());
    }

    // Get NFT mint from participation (copy to avoid borrow issues)
    let mut nft_mint = [0u8; 32];
    nft_mint.copy_from_slice(&participation_data[16..48]);

    // Verify NFT asset matches
    if nft_asset.key().as_ref() != &nft_mint {
        return Err(MiningError::InvalidNftMint.into());
    }

    // Verify winner owns the NFT (check owner in participation snapshot)
    let owner_at_join = &participation_data[48..80];
    if winner.key().as_ref() != owner_at_join {
        return Err(MiningError::NotNftOwner.into());
    }

    // Check claim status
    let hashrate_claimed = participation_data[113];
    let ticket_claimed = participation_data[114];

    // Check winner status (set by finalize_epoch)
    let won_hashrate_pool = participation_data[116];
    let won_ticket_pool = participation_data[117];

    // Derive lottery pool authority PDA
    let (expected_authority, authority_bump) =
        find_program_address(&[LOTTERY_POOL_SEEDS], program_id);
    if lottery_authority.key() != &expected_authority {
        return Err(MiningError::InvalidPdaSeeds.into());
    }

    let mut total_claim = 0u64;

    // Check if winner of hashrate pool
    let should_claim_hashrate = (claim_type == 0 || claim_type == 2) && won_hashrate_pool != 0;

    if should_claim_hashrate {
        if hashrate_claimed != 0 {
            return Err(MiningError::AlreadyClaimed.into());
        }
        // Split prize equally among all hashrate winners
        let share = if hashrate_winner_count > 0 {
            hashrate_pool / (hashrate_winner_count as u64)
        } else {
            0
        };
        total_claim = total_claim.saturating_add(share);
        participation_data[113] = 1; // Mark hashrate claimed
    }

    // Check if winner of ticket pool
    let should_claim_ticket = (claim_type == 1 || claim_type == 2) && won_ticket_pool != 0;

    if should_claim_ticket {
        if ticket_claimed != 0 {
            return Err(MiningError::AlreadyClaimed.into());
        }
        // Split prize equally among all ticket winners
        let share = if ticket_winner_count > 0 {
            ticket_pool_amount / (ticket_winner_count as u64)
        } else {
            0
        };
        total_claim = total_claim.saturating_add(share);
        participation_data[114] = 1; // Mark ticket claimed
    }

    // Verify there's something to claim
    if total_claim == 0 {
        return Err(MiningError::NoPrizeToClaim.into());
    }

    // Transfer prize from lottery pool to winner
    let bump_seed = [authority_bump];
    let signer_seeds = [
        Seed::from(LOTTERY_POOL_SEEDS),
        Seed::from(&bump_seed),
    ];
    let signer = Signer::from(&signer_seeds);

    pinocchio_token::instructions::Transfer {
        from: lottery_pool,
        to: winner_token_account,
        authority: lottery_authority,
        amount: total_claim,
    }
    .invoke_signed(&[signer])?;

    Ok(())
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_claim_type_parsing() {
        // Empty data = claim both
        let data: &[u8] = &[];
        let claim_type = if data.is_empty() { 2 } else { data[0] };
        assert_eq!(claim_type, 2);

        // 0 = hashrate only
        let data = &[0u8];
        let claim_type = if data.is_empty() { 2 } else { data[0] };
        assert_eq!(claim_type, 0);

        // 1 = ticket only
        let data = &[1u8];
        let claim_type = if data.is_empty() { 2 } else { data[0] };
        assert_eq!(claim_type, 1);
    }

    #[test]
    fn test_prize_splitting() {
        let hashrate_pool = 80_000_000_000u64; // 80 LODE
        let ticket_pool = 20_000_000_000u64; // 20 LODE

        // Single winner gets full pool
        let share = hashrate_pool / 1;
        assert_eq!(share, 80_000_000_000);

        // Two winners split 50/50
        let share = hashrate_pool / 2;
        assert_eq!(share, 40_000_000_000);

        // Three winners split
        let share = hashrate_pool / 3;
        assert_eq!(share, 26_666_666_666); // Integer division

        // Ten winners
        let share = hashrate_pool / 10;
        assert_eq!(share, 8_000_000_000);
    }

    #[test]
    fn test_both_pool_winner() {
        // Winner of both pools (rare but possible)
        let hashrate_pool = 80_000_000_000u64;
        let ticket_pool = 20_000_000_000u64;
        let hashrate_winner_count = 2u16;
        let ticket_winner_count = 1u16;

        let hashrate_share = hashrate_pool / (hashrate_winner_count as u64);
        let ticket_share = ticket_pool / (ticket_winner_count as u64);

        let total = hashrate_share + ticket_share;
        assert_eq!(total, 40_000_000_000 + 20_000_000_000);
        assert_eq!(total, 60_000_000_000);
    }
}
