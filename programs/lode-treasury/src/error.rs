//! LODE Treasury Program Errors

use pinocchio::program_error::ProgramError;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u32)]
pub enum TreasuryError {
    /// Invalid authority provided
    InvalidAuthority = 0,
    /// Treasury already initialized
    AlreadyInitialized = 1,
    /// Invalid PDA seeds
    InvalidPdaSeeds = 2,
    /// Arithmetic overflow
    Overflow = 3,
    /// Account not writable
    AccountNotWritable = 4,
    /// Account not signer
    AccountNotSigner = 5,
    /// Invalid fee split configuration
    InvalidFeeSplit = 6,
    /// No fees to harvest
    NoFeesToHarvest = 7,
    /// Invalid token mint
    InvalidMint = 8,
}

impl From<TreasuryError> for ProgramError {
    fn from(e: TreasuryError) -> Self {
        ProgramError::Custom(e as u32)
    }
}
