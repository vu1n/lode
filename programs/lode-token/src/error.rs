//! LODE Token Program Errors

use pinocchio::program_error::ProgramError;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u32)]
pub enum TokenError {
    /// Invalid authority provided
    InvalidAuthority = 0,
    /// Token config already initialized
    AlreadyInitialized = 1,
    /// Invalid PDA seeds
    InvalidPdaSeeds = 2,
    /// Arithmetic overflow
    Overflow = 3,
    /// Invalid transfer fee basis points (max 10000)
    InvalidTransferFeeBps = 4,
    /// Account not writable
    AccountNotWritable = 5,
    /// Account not signer
    AccountNotSigner = 6,
    /// Invalid mint account
    InvalidMintAccount = 7,
}

impl From<TokenError> for ProgramError {
    fn from(e: TokenError) -> Self {
        ProgramError::Custom(e as u32)
    }
}
