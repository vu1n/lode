//! LODE Mining Program Errors

use pinocchio::program_error::ProgramError;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u32)]
pub enum MiningError {
    /// Invalid authority provided
    InvalidAuthority = 0,
    /// Mining config already initialized
    AlreadyInitialized = 1,
    /// Invalid PDA seeds
    InvalidPdaSeeds = 2,
    /// Arithmetic overflow
    Overflow = 3,
    /// Account not writable
    AccountNotWritable = 4,
    /// Account not signer
    AccountNotSigner = 5,
    /// Invalid NFT mint
    InvalidNftMint = 6,
    /// NFT not owned by signer
    NotNftOwner = 7,
    /// Epoch not active
    EpochNotActive = 8,
    /// Epoch already finalized
    EpochAlreadyFinalized = 9,
    /// Rent not paid
    RentNotPaid = 10,
    /// Already joined epoch
    AlreadyJoinedEpoch = 11,
    /// Invalid epoch state
    InvalidEpochState = 12,
    /// No prize to claim
    NoPrizeToClaim = 13,
    /// Already claimed
    AlreadyClaimed = 14,
    /// Invalid hashrate amount
    InvalidHashrate = 15,
    /// Epoch not finalized
    EpochNotFinalized = 16,
    /// Grace period ended
    GracePeriodEnded = 17,
    /// Grace period expired
    GracePeriodExpired = 18,
    /// Rent already paid for this epoch
    RentAlreadyPaid = 19,
    /// Invalid account data
    InvalidAccountData = 20,
}

impl From<MiningError> for ProgramError {
    fn from(e: MiningError) -> Self {
        ProgramError::Custom(e as u32)
    }
}
