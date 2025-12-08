# LODE – Protocol Spec (TLA+ skeletons + PRD)

## Part 1 – TLA+ Specs (High-Level)


### 1.1 LODE Top-Level Module (Abstract)

---- MODULE LODE ----
EXTENDS Naturals, Sequences, FiniteSets

(*
  Abstract, high-level spec of the LODE protocol:
  - Token balances
  - Staked balances and time-weighting
  - Transfer fee harvesting and splitting
  - Pay-to-mine burn and hashrate
  - Daily mining epoch with randomized winners

  This is NOT a byte-accurate Solana spec; it's for reasoning about invariants.
*)

CONSTANTS
    Addresses,          \* finite set of user addresses
    SMax,               \* max total supply of LODE
    FeeBps,             \* transfer fee in basis points (e.g. 50)
    FeeMax,             \* max fee per transfer (in LODE units)
    Alpha, Beta, Gamma, \* fee split weights: burn / staking / lottery
    TMax, Tau,          \* time-multiplier params: max multiplier, time to max (epochs)
    mMax,               \* max ratio H_paid / H_stake
    EpochLength,        \* number of "steps" per epoch (abstract)
    Nwinners            \* number of winners per mining epoch


ASSUME Alpha + Beta + Gamma = 1

(*
  State variables
*)

VARIABLES
    balances,       \* [addr \in Addresses -> Nat]  - liquid LODE
    staked,         \* [addr \in Addresses -> Nat]  - staked LODE
    stakeEpoch,     \* [addr \in Addresses -> Nat]  - epoch index of last stake reset
    totalSupply,    \* Nat                          - current total minted LODE
    feeAccumulator, \* Nat                          - total fees collected but not yet harvested
    burned,         \* Nat                          - total burned LODE
    stakingPool,    \* Nat                          - LODE reserved for staking rewards
    lotteryPool,    \* Nat                          - LODE reserved for lottery/mining
    epoch,          \* Nat                          - current mining epoch index
    epochTick,      \* Nat                          - progress inside the epoch [0..EpochLength-1]
    paidBurn,       \* [addr \in Addresses -> Nat]  - LODE burned this epoch for paid hashrate
    winners,        \* SUBSET Addresses             - winners for current epoch (simplified)
    rewards         \* [addr \in Addresses -> Nat]  - claimable rewards per address (in LODE units, abstract)

(*
  Helper functions
*)

Fee(amount) ==
    LET raw == (amount * FeeBps) \div 10000
    IN IF raw > FeeMax THEN FeeMax ELSE raw

(*
  Time multiplier: T_i = 1 + (TMax - 1) * min(Δt / Tau, 1)
  We model time as integer epochs, so Δt = epoch - stakeEpoch[i].
  For simplicity, we cap T_i at TMax and keep it rational here, but
  in practice we'd represent with fixed-point.
*)

TimeMult(i) ==
    IF staked[i] = 0 THEN 1
    ELSE
        LET dt == epoch - stakeEpoch[i] IN
        IF dt >= Tau THEN TMax
        ELSE 1 + (TMax - 1) * dt / Tau

(*
  Baseline hashrate: H_stake_i = stake_i * T_i
*)

HStake(i) ==
    staked[i] * TimeMult(i)

(*
  Paid hashrate: H_paid_raw = kPaid * sqrt(burn_i)
  In abstract spec, we don’t care about absolute scale, only monotonicity
  and the cap H_paid_i <= mMax * H_stake_i. So we can model sqrt as a
  generic concave function over Nat, e.g., integer sqrt or any monotone concave.
*)

Concave(b) ==
    \* integer square root approximation
    CHOOSE r \in Nat : r * r <= b /\ (r+1)*(r+1) > b

HPaid(i) ==
    LET raw == Concave(paidBurn[i]) IN
        IF HStake(i) = 0 THEN 0
        ELSE Min(raw, mMax * HStake(i))

HTotal(i) ==
    HStake(i) + HPaid(i)

TotalHashrate ==
    LET S == { i \in Addresses : HTotal(i) > 0 }
    IN IF S = {} THEN 0 ELSE Sum({HTotal(i) : i \in S})

(*
  Utility: sum over a finite set
*)

Sum(S) ==
    IF S = {} THEN 0
    ELSE CHOOSE x \in S : TRUE + Sum(S \ {x})

Min(a, b) == IF a < b THEN a ELSE b

(*
  Invariants
*)

SupplyInvariant ==
    totalSupply <= SMax

ConservationInvariant ==
    totalSupply =
        burned
        + feeAccumulator
        + stakingPool
        + lotteryPool
        + Sum({ balances[i] : i \in Addresses })
        + Sum({ staked[i] : i \in Addresses })

NonNegativeInvariant ==
    /\ totalSupply \in Nat
    /\ burned \in Nat
    /\ feeAccumulator \in Nat
    /\ stakingPool \in Nat
    /\ lotteryPool \in Nat
    /\ \A i \in Addresses:
        /\ balances[i] \in Nat
        /\ staked[i] \in Nat
        /\ paidBurn[i] \in Nat

(*
  Initial state
*)

Init ==
    /\ totalSupply = 0
    /\ burned = 0
    /\ feeAccumulator = 0
    /\ stakingPool = 0
    /\ lotteryPool = 0
    /\ epoch = 0
    /\ epochTick = 0
    /\ \A i \in Addresses:
        /\ balances[i] = 0
        /\ staked[i] = 0
        /\ stakeEpoch[i] = 0
        /\ paidBurn[i] = 0
        /\ rewards[i] = 0
    /\ winners = {}

(*
  Actions
*)

(*
  Abstract mint into some address, respecting SMax and emission schedule.
  In practice controlled by emission logic.
*)
Mint(i, amt) ==
    /\ i \in Addresses
    /\ amt \in Nat
    /\ amt > 0
    /\ totalSupply + amt <= SMax
    /\ totalSupply' = totalSupply + amt
    /\ balances' = [balances EXCEPT ![i] = @ + amt]
    /\ UNCHANGED << staked, stakeEpoch, feeAccumulator, burned,
                    stakingPool, lotteryPool, epoch, epochTick,
                    paidBurn, winners, rewards >>

(*
  Transfer LODE from a -> b, applying token-level fee.
*)

Transfer(a, b, amt) ==
    /\ a \in Addresses /\ b \in Addresses
    /\ amt \in Nat /\ amt > 0
    /\ balances[a] >= amt
    /\ LET fee == Fee(amt) IN
        /\ balances' =
            [balances EXCEPT
                ![a] = @ - amt,
                ![b] = @ + (amt - fee)]
        /\ feeAccumulator' = feeAccumulator + fee
    /\ UNCHANGED << staked, stakeEpoch, totalSupply, burned,
                    stakingPool, lotteryPool, epoch, epochTick,
                    paidBurn, winners, rewards >>

(*
  Stake: move from balances to staked, pay transfer fee abstractly as already charged by Transfer.
  We assume that by the time Stake is called, balances reflect the net effect.
*)

Stake(i, amt) ==
    /\ i \in Addresses
    /\ amt \in Nat /\ amt > 0
    /\ balances[i] >= amt
    /\ balances' = [balances EXCEPT ![i] = @ - amt]
    /\ staked'   = [staked   EXCEPT ![i] = @ + amt]
    /\ stakeEpoch' = [stakeEpoch EXCEPT ![i] = epoch]
    /\ UNCHANGED << totalSupply, feeAccumulator, burned,
                    stakingPool, lotteryPool, epoch, epochTick,
                    paidBurn, winners, rewards >>

(*
  Unstake: move from staked back to balances.
  Any transfer fee impact is handled via Transfer; here we model the logical move.
*)

Unstake(i, amt) ==
    /\ i \in Addresses
    /\ amt \in Nat /\ amt > 0
    /\ staked[i] >= amt
    /\ staked'   = [staked EXCEPT ![i] = @ - amt]
    /\ balances' = [balances EXCEPT ![i] = @ + amt]
    /\ stakeEpoch' = [stakeEpoch EXCEPT ![i] = epoch]
    /\ UNCHANGED << totalSupply, feeAccumulator, burned,
                    stakingPool, lotteryPool, epoch, epochTick,
                    paidBurn, winners, rewards >>

(*
  Harvest fees: split feeAccumulator into burn / staking / lottery.
*)

HarvestFees ==
    /\ feeAccumulator > 0
    /\ LET f == feeAccumulator IN
        /\ burned'       = burned + (Alpha * f)
        /\ stakingPool'  = stakingPool + (Beta  * f)
        /\ lotteryPool'  = lotteryPool + (Gamma * f)
        /\ totalSupply'  = totalSupply - (Alpha * f)
        /\ feeAccumulator' = 0
    /\ UNCHANGED << balances, staked, stakeEpoch,
                    epoch, epochTick, paidBurn,
                    winners, rewards >>

(*
  Pay-to-mine: burn LODE from balances, increase paidBurn[i].
*)

PayToMine(i, amt) ==
    /\ i \in Addresses
    /\ amt \in Nat /\ amt > 0
    /\ balances[i] >= amt
    /\ staked[i] > 0 \* must stake to mine
    /\ balances' = [balances EXCEPT ![i] = @ - amt]
    /\ burned'   = burned + amt
    /\ totalSupply' = totalSupply - amt
    /\ paidBurn' = [paidBurn EXCEPT ![i] = @ + amt]
    /\ UNCHANGED << staked, stakeEpoch, feeAccumulator,
                    stakingPool, lotteryPool, epoch, epochTick,
                    winners, rewards >>

(*
  EpochTick: internal stepping; when epochTick hits EpochLength-1,
  we finalize the epoch by drawing winners and distributing rewards.
*)

AdvanceTick ==
    /\ epochTick < EpochLength - 1
    /\ epochTick' = epochTick + 1
    /\ UNCHANGED << epoch, balances, staked, stakeEpoch,
                    totalSupply, feeAccumulator, burned,
                    stakingPool, lotteryPool, paidBurn,
                    winners, rewards >>

(*
  End-of-epoch: compute R_epoch, draw winners, allocate rewards, reset epoch state.
  Randomness is abstracted as a nondeterministic choice of winners with probability
  proportional to HTotal(i).
*)

EndEpoch ==
    /\ epochTick = EpochLength - 1
    /\ LET
          active == { i \in Addresses : staked[i] >= 0 /\ HTotal(i) > 0 }
          \* For simplicity, we model R_epoch as lotteryPool; emissions can be modeled separately.
          R_epoch == lotteryPool
       IN
       /\ active # {} \* at least one miner
       /\ winners' \in SUBSET active
       /\ Cardinality(winners') <= Nwinners
       /\ \A i \in winners': rewards'[i] = rewards[i] + R_epoch \div Cardinality(winners')
       /\ lotteryPool' = 0
       /\ epoch' = epoch + 1
       /\ epochTick' = 0
       /\ paidBurn' = [i \in Addresses |-> 0]
       /\ UNCHANGED << balances, staked, stakeEpoch,
                       totalSupply, feeAccumulator, burned,
                       stakingPool >>
       
(*
  Claim rewards: move from rewards balance to on-chain LODE balances.
*)

Claim(i) ==
    /\ i \in Addresses
    /\ rewards[i] > 0
    /\ balances' = [balances EXCEPT ![i] = @ + rewards[i]]
    /\ rewards'  = [rewards EXCEPT ![i] = 0]
    /\ UNCHANGED << staked, stakeEpoch, totalSupply,
                    feeAccumulator, burned, stakingPool,
                    lotteryPool, epoch, epochTick,
                    paidBurn, winners >>

(*
  Next-state relation
*)

Next ==
    \/ \E i, j, amt \in Addresses \X Addresses \X Nat : Transfer(i, j, amt)
    \/ \E i, amt \in Addresses \X Nat : Stake(i, amt)
    \/ \E i, amt \in Addresses \X Nat : Unstake(i, amt)
    \/ HarvestFees
    \/ \E i, amt \in Addresses \X Nat : PayToMine(i, amt)
    \/ AdvanceTick
    \/ EndEpoch
    \/ \E i \in Addresses : Claim(i)
    \/ \E i, amt \in Addresses \X Nat : Mint(i, amt)

Spec ==
    Init /\ [][Next]_<<balances, staked, stakeEpoch, totalSupply,
                    feeAccumulator, burned, stakingPool, lotteryPool,
                    epoch, epochTick, paidBurn, winners, rewards>>

Inv ==
    SupplyInvariant /\ ConservationInvariant /\ NonNegativeInvariant

====


### 1.2 Optional Refinement: Staking+Mining Only

You can split the above into modules if you want a more focused spec, e.g.:

- `LODEToken` – only Transfer + Fee + Mint + Burn
- `LODEStaking` – refinement that assumes a token module and adds stake/unstake + time weighting
- `LODEMining` – assumes both and reasons about mining epochs, pay-to-mine, and rewards

For now, the monolithic module is enough to:

- check invariants (no negative balances, supply cap),
- assert properties like “paid hashrate never exceeds mMax * H_stake”,
- reason about the effect of different Alpha/Beta/Gamma, FeeBps, mMax etc.


## Part 2 – Product Requirements Document (PRD)


# LODE – Gamified Gold on Solana  
## Product Requirements Document (PRD v1)

### 1. Overview

**Product name:** LODE  
**Tagline:** Gamified Gold on Solana  
**Type:** On-chain protocol + web app

LODE is a **store-of-value token** on Solana that uses:

- **Bitcoin-style emission + halving**,  
- a **token-level transfer fee** that funds burns and rewards,  
- and a **daily mining lottery** where users can stake and burn LODE to compete for jackpots.

The goal is to create a digital asset that feels like “gold on Solana” but stays engaging through a simple, transparent game loop rather than complex DeFi strategies.

---

### 2. Goals & Non-Goals

#### 2.1 Goals

- **G1: Store-of-Value Narrative**
  - Hard-capped supply.
  - Predictable decaying emission schedule.
  - Multiple burn vectors that make supply scarcer as usage grows.

- **G2: Daily Engagement**
  - Users should have a reason to check LODE at least once per day.
  - Actions: stake, optionally burn a bit to boost, check if they won.

- **G3: Fair-ish Mining Game**
  - Large holders should win more often, but small holders must sometimes win.
  - Sybil attacks (wallet splitting) should not be rewarded.
  - Paid boosts should require real stake (“miners must be investors”).

- **G4: Simple, Auditable v1**
  - Keep protocol logic minimal for initial audits and security.
  - Push complexity (tiers, jackpot rollovers, exotic boosts) to v2+.

#### 2.2 Non-Goals (v1)

- Not a generic DeFi yield aggregator.
- Not a governance token in v1 (governance can be added later).
- Not a payments token; high-velocity use cases are out-of-scope.
- No leverage, lending, or rehypothecation of staked LODE in v1.

---

### 3. Personas

1. **“Diamond Hands DeFi User”**
   - Holds SOL, BTC, ETH, etc.
   - Wants a higher-upside SoV bet.
   - Okay with mild complexity but not a full degen yield farm.

2. **“Gamer / Lottery Enjoyer”**
   - Likes on-chain games, mints, PoolTogether, etc.
   - Motivated by jackpots and streaks.
   - Wants to see their address win sometimes.

3. **“Protocol Power User / Whale”**
   - Large capital.
   - Will stake significant LODE.
   - Will optimize pay-to-mine vs expected EV of jackpots.

4. **“Builder / Integrator”**
   - Wants to integrate LODE stats into dashboards, bots, or DeFi overlays.
   - Needs simple APIs & program interfaces.

---

### 4. Core User Stories

#### 4.1 Acquisition & Staking

- **US1:** As a user, I can buy LODE via presale or DEX and see my balance.
- **US2:** As a user, I can stake my LODE into a vault and see:
  - my staked amount,
  - my time multiplier,
  - my effective “mining power”.

- **US3:** As a user, I can unstake part or all of my LODE, understanding that:
  - I pay the normal transfer fee,
  - my time multiplier resets.

#### 4.2 Mining & Lottery

- **US4:** As a staker, I am automatically entered into the daily mining lottery, with odds proportional to my mining power.
- **US5:** As a staker, I can optionally burn LODE (“Boost”) during a given day to temporarily increase my mining power, up to some cap.
- **US6:** As a staker, I can see:
  - the current jackpot size (per epoch),
  - time remaining in the epoch,
  - my estimated probability of winning at least once.

#### 4.3 Rewards

- **US7:** As a winner, I can see:
  - that I won in a given day,
  - how much I won,
  - a breakdown by asset (LODE, SOL, USDC).

- **US8:** As a winner, I can claim my rewards via one-click transaction (or a simple button in the dApp), paying normal network fees.

- **US9:** As a staker who hasn’t won recently, I still see:
  - cumulative fee-based yield on my stake,
  - clear indication of time multiplier progress.

#### 4.4 Transparency & Safety

- **US10:** As a user, I can inspect:
  - total supply and burned LODE,
  - transfer fee rate and historical fees collected,
  - emissions schedule and remaining emission bucket,
  - historical jackpot sizes and winners.

- **US11:** As a technical user, I can:
  - review audited program source code,
  - follow TLA+/spec docs to understand core invariants.

---

### 5. Functional Requirements

#### 5.1 Token

- **FR-T1:** LODE must be a Token-2022 SPL mint with:
  - hard-capped supply,
  - TransferFee extension configured with initial fee (0.50%, max 100 LODE).

- **FR-T2:** Every transfer of LODE must apply the transfer fee and route withheld fees to the Treasury withdraw authority.

- **FR-T3:** There is no fee exemption for staking or mining-related transfers in v1.

#### 5.2 Treasury & Fee Split

- **FR-TR1:** Treasury program must be able to:
  - withdraw all accumulated fees from the token program,
  - compute burn/staking/lottery allocations (α, β, γ),
  - execute token burns and transfers to staking and mining vaults.

- **FR-TR2:** Fee split multipliers must be stored on-chain and upgradable via a controlled mechanism (e.g. governed or hard-coded in v1).

#### 5.3 Staking

- **FR-S1:** Users can stake LODE by sending it to the staking program (UI should wrap this; on-chain it’s CPI + token transfer).

- **FR-S2:** Staking program must:
  - track per-user stake amount,
  - track a per-user `stake_since_epoch`,
  - enforce minimum stake for mining participation (`S_min`).

- **FR-S3:** Unstake must:
  - decrease staked amount,
  - move LODE back to user wallet,
  - reset time multiplier for the remaining stake.

- **FR-S4:** Staking program must periodically receive staking rewards from Treasury and distribute them pro-rata or allow users to claim their share.

#### 5.4 Mining / Lottery

- **FR-M1:** Mining program must:
  - define daily epochs,
  - snapshot staker state per epoch,
  - track per-user burned LODE for pay-to-mine within the epoch.

- **FR-M2:** Mining program must request randomness from VRF for each epoch and store the seed to be used in winner selection.

- **FR-M3:** Winner selection must:
  - be proportional to HTotal(i),
  - choose `N_winners` unique addresses (or allow repeated wins, this must be decide-able),
  - allocate rewards according to a configurable payout schedule.

- **FR-M4:** Mining program must:
  - maintain per-user pending rewards,
  - expose a `claim()` instruction that transfers rewards from vaults to user wallets.

- **FR-M5:** Pay-to-mine must:
  - burn LODE from the user,
  - increase user’s paid hashrate for the current epoch,
  - enforce `H_paid_i <= m_max * H_stake_i`.

#### 5.5 Frontend / UX

- **FR-UI1:** Dashboard shows:
  - user wallet balances (LODE), staked LODE, multiplier, hashrate,
  - current epoch countdown and jackpot size,
  - personal summary: “You have X% chance of winning at least once today” (approx).

- **FR-UI2:** Actions:
  - stake / unstake,
  - boost (burn LODE to increase mining power),
  - claim rewards,
  - view history of wins and claims.

- **FR-UI3:** Transparency:
  - total burned LODE,
  - transfer fee rate & lifetime fees,
  - remaining emissions.

---

### 6. Non-Functional Requirements

- **NFR-1:** Gas efficiency: keep all instructions within reasonable CU limits on Solana mainnet.
- **NFR-2:** Security:
  - third-party audit before mainnet launch,
  - formal reasoning on supply & reward invariants (using TLA+ and/or other methods).
- **NFR-3:** Composability: avoid custom token program forks; rely on Token-2022 only.
- **NFR-4:** Upgradability:
  - programs may be upgradable with strict controls,
  - token fee parameters can be adjusted via governance or a multisig.

---

### 7. Success Metrics

- **SM-1:** % of circulating LODE staked.
- **SM-2:** Daily active unique addresses interacting (stake/boost/claim).
- **SM-3:** Average jackpot size and variance.
- **SM-4:** Long-term net deflation rate after emissions slow.
- **SM-5:** Protocol safety: 0 critical exploits, 0 loss-of-funds incidents.

---

### 8. Open Questions & Design Knobs

- Final choice of:
  - transfer fee (0.25% vs 0.50%),
  - fee split (40/10/50 vs nearby),
  - halving period (4 years vs faster),
  - number of winners per epoch and payout curve,
  - how aggressively to pay in SOL/USDC vs LODE.

- Governance model for parameters:
  - multisig vs token governance,
  - how to safely evolve parameters without breaking SoV narrative.

- Marketing/UX:
  - do we introduce “jackpot rollover” early,
  - how we message “burn to mine” so it’s intuitive, not scary.

---

End of PRD
