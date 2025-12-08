//! LODE Protocol v2 - Token Program
//!
//! Manages the LODE token (Token-2022) configuration and mint authority.
//! - Creates Token-2022 mint with TransferFee extension (0.5%)
//! - Stores TokenConfig PDA with protocol parameters
//! - Hard cap: 21,000,000 LODE (9 decimals)

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
        _ => Err(ProgramError::InvalidInstructionData),
    }
}

// Program ID - ANxSnSKr6VBXw7dEaW9P3utWbXxoH2jxctgA1sXtPyL8
pinocchio_pubkey::declare_id!("ANxSnSKr6VBXw7dEaW9P3utWbXxoH2jxctgA1sXtPyL8");
