# LODE Protocol TLA+ Specifications

This directory contains formal specifications for the LODE mining protocol written in TLA+ (Temporal Logic of Actions).

## Specifications

### 1. LodeMining.tla
**Core mining and lottery invariants**

Models the fundamental staking and hashrate mechanics:
- **Variables**: supply, totalEmitted, totalBurned, epoch, stakes, bookedHashrate, bootingHashrate
- **Key Invariants**:
  - `TypeInvariant`: All variables have correct types
  - `SupplyConservation`: supply = InitialSupply + totalEmitted - totalBurned
  - `HashrateCap`: Total permanent hashrate ≤ stake_hashrate for all users
  - `NoNegativeBalances`: All balances are non-negative
- **Actions**: Stake, Unstake, BuyHashrate, MarketBuyHashrate, SellHashrate, AdvanceEpoch

### 2. LodeEmissions.tla
**Emission schedule with halving and tail emission**

Models the token emission over time:
- **Constants**: MAX_SUPPLY (210M), TAIL_EMISSION_BPS (30), HALVING_INTERVAL (52 weeks)
- **Variables**: currentWeek, totalEmitted, currentSupply, halvingPhase
- **Key Invariants**:
  - `EmissionCap`: totalEmitted ≤ 40% of MAX_SUPPLY during halving phase
  - `TailEmissionRate`: After year 8, daily emission = supply × 30 bps / 365
  - `SupplyCap`: Supply never exceeds MAX_SUPPLY
- **Actions**: AdvanceEpoch, MintEmission

### 3. HashrateMarket.tla
**Hashrate marketplace mechanics**

Models the hashrate listing and trading system:
- **Variables**: listings, lockedHashrate, bookedHashrate, bootingHashrate
- **Key Invariants**:
  - `LockedMatchesListings`: Sum of listing amounts = lockedHashrate per user
  - `OnlyBootedSellable`: Cannot list more than booted - locked hashrate
  - `MarketBuyInstant`: Market-bought hashrate is immediately booted
  - `UniqueListingIds`: All listings have unique identifiers
- **Actions**: ListHashrate, BuyListedHashrate, CancelListing, CompleteBooting

## Running the Specifications

### Prerequisites
Install the TLA+ toolbox from: https://lamport.azurewebsites.net/tla/toolbox.html

Or use the command-line tools:
```bash
# Install TLA+ tools
brew install tlaplus  # macOS
# or download from https://github.com/tlaplus/tlaplus/releases
```

### Model Checking

Each specification has a corresponding `.cfg` configuration file with appropriate constants and invariants.

#### Check LodeMining:
```bash
tlc LodeMining.tla -config LodeMining.cfg
```

#### Check LodeEmissions:
```bash
tlc LodeEmissions.tla -config LodeEmissions.cfg
```

#### Check HashrateMarket:
```bash
tlc HashrateMarket.tla -config HashrateMarket.cfg
```

### Using TLA+ Toolbox (GUI)

1. Open TLA+ Toolbox
2. Create a new specification for each `.tla` file
3. Create a new model using the corresponding `.cfg` file
4. Run the model checker to verify invariants and properties

## Key Concepts

### Halving Schedule
- 8 phases of 52 weeks each (8 years total)
- Each phase emits half of the previous phase
- Total emission during halving: 40% of MAX_SUPPLY

### Tail Emission
- Starts after year 8 (week 416)
- Daily emission = current_supply × 30 bps / 365
- Ensures perpetual mining incentive

### Hashrate States
- **Booting**: Newly purchased hashrate (7-day wait)
- **Booked**: Permanent hashrate (can be listed for sale)
- **Locked**: Booked hashrate in active marketplace listings

### Market Mechanics
- Direct purchases: Enter booting period
- Market purchases: Instantly booted
- Only booted hashrate can be listed
- Listings lock the hashrate until sold or cancelled

## Verification Strategy

The specifications verify:
1. **Safety properties**: Invariants that must always hold
2. **Liveness properties**: Things that must eventually happen
3. **Fairness**: Ensuring progress under fair scheduling

### Example Verification Results

When model checking succeeds, TLC will verify:
- No violation of supply conservation
- No way to exceed hashrate caps
- No way to create negative balances
- Proper emission rate transitions
- Marketplace consistency

## Extending the Specifications

To add new features:
1. Define new variables in the VARIABLES section
2. Update TypeInvariant with new type constraints
3. Add new invariants to capture desired properties
4. Define new actions that modify the variables
5. Update Next to include new actions
6. Add corresponding tests in the .cfg file

## References

- [TLA+ Homepage](https://lamport.azurewebsites.net/tla/tla.html)
- [Learn TLA+](https://learntla.com/)
- [TLA+ Video Course](https://lamport.azurewebsites.net/video/videos.html)
- [Specifying Systems Book](https://lamport.azurewebsites.net/tla/book.html)
