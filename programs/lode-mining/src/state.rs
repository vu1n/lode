//! LODE Mining Program State

/// Mining configuration PDA
/// Seeds: ["mining_config"]
///
/// Size: 8 + 32 + 8 + 8 + 8 + 8 + 8 + 2 + 2 + 8 + 8 + 1 + 7 = 108 bytes
#[repr(C)]
pub struct MiningConfig {
    /// Discriminator for account type
    pub discriminator: [u8; 8],
    /// Authority that can update config
    pub authority: [u8; 32],
    /// Current epoch ID
    pub current_epoch: u64,
    /// Epoch duration in seconds
    pub epoch_duration: u64,
    /// Base rent per NFT per epoch (in LODE smallest units)
    pub base_rent: u64,
    /// Hashrate rent rate in basis points (10 = 0.1% of hashrate)
    pub hashrate_rent_bps: u16,
    /// Grace period for rent payment (% of epoch duration, e.g., 10 = 10%)
    pub grace_period_pct: u8,
    /// Age bonus per epoch in basis points (100 = 1%)
    pub age_bonus_bps: u16,
    /// Maximum age bonus in basis points (5000 = 50%)
    pub max_age_bonus_bps: u16,
    /// Base mint cost in LODE
    pub base_mint_cost: u64,
    /// Genesis timestamp
    pub genesis_timestamp: i64,
    /// PDA bump seed
    pub bump: u8,
    /// Padding for alignment
    pub _padding: [u8; 6],
}

impl MiningConfig {
    pub const DISCRIMINATOR: [u8; 8] = *b"mineconf";
    pub const SIZE: usize = 108;
    pub const SEEDS: &'static [u8] = b"mining_config";

    /// Default epoch duration: 24 hours
    pub const DEFAULT_EPOCH_DURATION: u64 = 86400;

    /// Default base rent: 1 LODE (with 9 decimals)
    pub const DEFAULT_BASE_RENT: u64 = 1_000_000_000;

    /// Default hashrate rent: 0.01% (1 basis point)
    pub const DEFAULT_HASHRATE_RENT_BPS: u16 = 1;

    /// Default grace period: 10% of epoch
    pub const DEFAULT_GRACE_PERIOD_PCT: u8 = 10;

    /// Default age bonus per epoch: 1% (100 bps)
    pub const DEFAULT_AGE_BONUS_BPS: u16 = 100;

    /// Default max age bonus: 50% (5000 bps)
    pub const DEFAULT_MAX_AGE_BONUS_BPS: u16 = 5000;

    /// Default base mint cost: 100 LODE
    pub const DEFAULT_BASE_MINT_COST: u64 = 100_000_000_000;
}

/// Epoch state PDA
/// Seeds: ["epoch", epoch_id_bytes]
///
/// Hash/mask-based mining simulation:
/// - VRF generates random target each epoch
/// - Each NFT's hashrate determines mask permissiveness
/// - Multiple winners possible (split prize) or no winner (rollover)
///
/// Size: 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 4 + 1 + 1 + 8 + 8 + 8 + 2 + 2 + 4 = 104 bytes
#[repr(C)]
pub struct Epoch {
    /// Discriminator for account type
    pub discriminator: [u8; 8],
    /// Epoch ID
    pub epoch_id: u64,
    /// Start timestamp
    pub start_timestamp: i64,
    /// End timestamp
    pub end_timestamp: i64,
    /// Prize pool for hashrate winners (80%) - includes rollover
    pub hashrate_pool: u64,
    /// Prize pool for lucky ticket winners (20%) - includes rollover
    pub ticket_pool: u64,
    /// Total hashrate registered this epoch
    pub total_hashrate: u64,
    /// Rollover from previous epoch (no winners)
    pub rollover_amount: u64,
    /// Total participants (for lucky tickets)
    pub total_participants: u32,
    /// Epoch state: 0 = pending, 1 = active, 2 = finalized
    pub state: u8,
    /// PDA bump seed
    pub bump: u8,
    /// VRF seed used for randomness (the "target" to match)
    pub vrf_seed: u64,
    /// Total weighted hashrate (with age bonus) for winner selection
    pub total_weighted_hashrate: u64,
    /// Mining difficulty (higher = harder to hit, adjustable)
    pub difficulty: u64,
    /// Number of hashrate pool winners this epoch
    pub hashrate_winner_count: u16,
    /// Number of ticket pool winners this epoch
    pub ticket_winner_count: u16,
    /// Padding
    pub _padding: [u8; 4],
}

impl Epoch {
    pub const DISCRIMINATOR: [u8; 8] = *b"epoch___";
    pub const SIZE: usize = 104;
    pub const SEEDS_PREFIX: &'static [u8] = b"epoch";

    /// Epoch states
    pub const STATE_PENDING: u8 = 0;
    pub const STATE_ACTIVE: u8 = 1;
    pub const STATE_FINALIZED: u8 = 2;

    /// Pool allocations in basis points (80/20 split)
    pub const HASHRATE_POOL_BPS: u16 = 8000;
    pub const TICKET_POOL_BPS: u16 = 2000;

    /// Default mining difficulty (higher = harder to hit)
    /// At difficulty 10, a miner with hashrate H generates mask with ~H/10 permissive bits
    /// Calibrated so average expected winners ~= 1 at launch hashrate
    pub const DEFAULT_DIFFICULTY: u64 = 1_000_000;

    /// Maximum winners per pool (to prevent gas exhaustion on claims)
    pub const MAX_WINNERS_PER_POOL: u16 = 100;
}

/// Epoch participation PDA (per NFT per epoch)
/// Seeds: ["participation", epoch_id_bytes, nft_mint]
///
/// Hash/mask mining: After finalize_epoch, won_hashrate_pool and won_ticket_pool
/// are set to 1 if this NFT's "key" matched the target within its mask.
///
/// Size: 8 + 8 + 32 + 32 + 8 + 8 + 8 + 8 + 1 + 1 + 1 + 1 + 1 + 1 + 2 = 120 bytes
#[repr(C)]
pub struct EpochParticipation {
    /// Discriminator for account type
    pub discriminator: [u8; 8],
    /// Epoch ID
    pub epoch_id: u64,
    /// NFT mint address
    pub nft_mint: [u8; 32],
    /// Owner at time of joining (snapshot)
    pub owner_at_join: [u8; 32],
    /// Hashrate at time of joining (snapshot from NFT)
    pub hashrate_at_join: u64,
    /// Timestamp when joined
    pub joined_at: i64,
    /// Effective hashrate (after time-based scaling)
    pub effective_hashrate: u64,
    /// Weighted hashrate (with age bonus applied)
    pub weighted_hashrate: u64,
    /// Whether rent has been paid
    pub rent_paid: u8,
    /// Whether hashrate pool prize has been claimed
    pub hashrate_claimed: u8,
    /// Whether ticket pool prize has been claimed
    pub ticket_claimed: u8,
    /// PDA bump seed
    pub bump: u8,
    /// Whether this NFT won the hashrate pool (set by finalize_epoch)
    pub won_hashrate_pool: u8,
    /// Whether this NFT won the ticket pool (set by finalize_epoch)
    pub won_ticket_pool: u8,
    /// Padding
    pub _padding: [u8; 2],
}

impl EpochParticipation {
    pub const DISCRIMINATOR: [u8; 8] = *b"particip";
    pub const SIZE: usize = 120;
    pub const SEEDS_PREFIX: &'static [u8] = b"participation";
}

/// Emission schedule constants (from TLA+ spec)
pub struct EmissionSchedule;

impl EmissionSchedule {
    /// Initial weekly emission: 40,000 LODE
    pub const INITIAL_WEEKLY_EMISSION: u64 = 40_000_000_000_000;

    /// Halving interval: 208 weeks (4 years)
    pub const HALVING_INTERVAL_WEEKS: u64 = 208;

    /// Tail emission start: 8 years (416 weeks)
    pub const TAIL_EMISSION_START_WEEKS: u64 = 416;

    /// Tail emission rate: 0.3% per year (30 bps)
    pub const TAIL_EMISSION_BPS: u16 = 30;

    /// Calculate weekly emission for a given week
    pub fn weekly_emission(week: u64, current_supply: u64) -> u64 {
        if week >= Self::TAIL_EMISSION_START_WEEKS {
            // Tail emission: 0.3% of current supply per year, divided by 52 weeks
            let annual = current_supply * (Self::TAIL_EMISSION_BPS as u64) / 10000;
            annual / 52
        } else {
            // Halving schedule
            let halvings = week / Self::HALVING_INTERVAL_WEEKS;
            Self::INITIAL_WEEKLY_EMISSION >> halvings
        }
    }
}
