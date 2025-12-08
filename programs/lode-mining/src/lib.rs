//! LODE Mining Program
//!
//! NFT miner creation, upgrades, rent, epoch participation, and lottery.

pub mod error;
pub mod instructions;
pub mod mpl_core;
pub mod state;

use instructions::*;
use pinocchio::{
    account_info::AccountInfo, entrypoint, program_error::ProgramError, pubkey::Pubkey,
    ProgramResult,
};

entrypoint!(process_instruction);

pub fn process_instruction(
    program_id: &Pubkey,
    accounts: &[AccountInfo],
    instruction_data: &[u8],
) -> ProgramResult {
    if instruction_data.is_empty() {
        return Err(ProgramError::InvalidInstructionData);
    }

    match instruction_data[0] {
        0 => initialize::process(program_id, accounts, &instruction_data[1..]),
        1 => mint_miner::process(program_id, accounts, &instruction_data[1..]),
        2 => upgrade_miner::process(program_id, accounts, &instruction_data[1..]),
        3 => pay_rent::process(program_id, accounts, &instruction_data[1..]),
        4 => join_epoch::process(program_id, accounts, &instruction_data[1..]),
        5 => advance_epoch::process(program_id, accounts, &instruction_data[1..]),
        6 => finalize_epoch::process(program_id, accounts, &instruction_data[1..]),
        7 => claim::process(program_id, accounts, &instruction_data[1..]),
        _ => Err(ProgramError::InvalidInstructionData),
    }
}

pinocchio_pubkey::declare_id!("CSrYQ2uEURizXFDruLVyHUXcNN1Dv3XKFdbPnddMF2pB");
