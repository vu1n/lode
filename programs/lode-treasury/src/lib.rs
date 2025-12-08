//! LODE Treasury Program
//!
//! Handles fee harvesting and distribution:
//! - 30% burn (deflation)
//! - 50% lottery pool
//! - 20% POL (protocol-owned liquidity)

pub mod error;
pub mod instructions;
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
        1 => harvest::process(program_id, accounts, &instruction_data[1..]),
        _ => Err(ProgramError::InvalidInstructionData),
    }
}

pinocchio_pubkey::declare_id!("HjRCbiKYNa61Mee6Hbxy5tGCPzDBrzNcaZjVRGcPcSFC");
