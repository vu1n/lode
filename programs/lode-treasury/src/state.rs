//! LODE Treasury Program State

/// Treasury configuration PDA
/// Seeds: ["treasury"]
///
/// Size: 8 + 32 + 32 + 2 + 2 + 2 + 8 + 8 + 8 + 1 + 7 = 110 bytes
#[repr(C)]
pub struct Treasury {
    /// Discriminator for account type
    pub discriminator: [u8; 8],
    /// Authority that can update treasury config
    pub authority: [u8; 32],
    /// LODE token mint
    pub mint: [u8; 32],
    /// Burn percentage in basis points (3000 = 30%)
    pub burn_bps: u16,
    /// Lottery pool percentage in basis points (5000 = 50%)
    pub lottery_bps: u16,
    /// POL (treasury) percentage in basis points (2000 = 20%)
    pub treasury_bps: u16,
    /// Total burned via treasury
    pub total_burned: u64,
    /// Total sent to lottery pool
    pub total_to_lottery: u64,
    /// Total accumulated for POL
    pub total_to_pol: u64,
    /// PDA bump seed
    pub bump: u8,
    /// Padding for alignment
    pub _padding: [u8; 7],
}

impl Treasury {
    /// Account discriminator
    pub const DISCRIMINATOR: [u8; 8] = *b"treasury";

    /// Size of the Treasury account
    pub const SIZE: usize = 110;

    /// PDA seeds
    pub const SEEDS: &'static [u8] = b"treasury";

    /// Default burn percentage: 30% (3000 basis points)
    pub const DEFAULT_BURN_BPS: u16 = 3000;

    /// Default lottery percentage: 50% (5000 basis points)
    pub const DEFAULT_LOTTERY_BPS: u16 = 5000;

    /// Default POL percentage: 20% (2000 basis points)
    pub const DEFAULT_TREASURY_BPS: u16 = 2000;

    /// Maximum basis points (100%)
    pub const MAX_BPS: u16 = 10000;

    /// Validate that fee split adds up to 100%
    pub fn validate_fee_split(burn_bps: u16, lottery_bps: u16, treasury_bps: u16) -> bool {
        burn_bps.saturating_add(lottery_bps).saturating_add(treasury_bps) == Self::MAX_BPS
    }
}
