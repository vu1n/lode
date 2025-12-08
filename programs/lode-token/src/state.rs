//! LODE Token Program State

/// Token configuration PDA
/// Seeds: ["token_config"]
///
/// Size: 8 + 32 + 32 + 8 + 2 + 1 + 7 = 90 bytes
#[repr(C)]
pub struct TokenConfig {
    /// Discriminator for account type
    pub discriminator: [u8; 8],
    /// The LODE token mint (Token-2022)
    pub mint: [u8; 32],
    /// Authority that can update config
    pub authority: [u8; 32],
    /// Maximum supply in smallest units (21M * 10^9)
    pub max_supply: u64,
    /// Transfer fee in basis points (50 = 0.5%)
    pub transfer_fee_bps: u16,
    /// PDA bump seed
    pub bump: u8,
    /// Padding for alignment
    pub _padding: [u8; 7],
}

impl TokenConfig {
    /// Account discriminator
    pub const DISCRIMINATOR: [u8; 8] = *b"tokencfg";

    /// Size of the TokenConfig account
    pub const SIZE: usize = 90;

    /// PDA seeds
    pub const SEEDS: &'static [u8] = b"token_config";

    /// Maximum supply: 21,000,000 LODE with 9 decimals
    pub const MAX_SUPPLY: u64 = 21_000_000_000_000_000;

    /// Default transfer fee: 0.5% (50 basis points)
    pub const DEFAULT_TRANSFER_FEE_BPS: u16 = 50;

    /// Token decimals
    pub const DECIMALS: u8 = 9;

    /// Maximum transfer fee in basis points (100% = 10000)
    pub const MAX_FEE_BPS: u16 = 10000;
}
