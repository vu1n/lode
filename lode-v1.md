# LODE – Gamified Gold on Solana

**Economic Design v1.0 (for feedback)**

**Chain:** Solana (Token-2022)
**Ticker:** `LODE`
**Thesis:** *Gamified Gold* – a deflationary store-of-value with Bitcoin-style scarcity and a daily “mining lottery” you can participate in by staking and burning.

---

## 1. Core Idea

LODE is a Store of Value (SoV) that **requires action** to stay interesting:

* You **stake** LODE to gain “mining power”.
* You can **burn** extra LODE (“pay for hashrate”) to boost your odds.
* Every day, the protocol pays out “block rewards” (emissions + fee revenue) via a on-chain lottery.
* Every movement and mining attempt pushes **deflation**: supply shrinks over time.

Key design goals:

1. **Sybil-safe** and whale-aware (no obvious wallet-splitting exploits).
2. **Simple enough** to implement + audit for v1.
3. **Clear SoV story**: hard cap, halving emissions, protocol-wide burn via Token-2022.

---

## 2. Components Overview

* **LODE Token (Token-2022 SPL mint)**

  * Hard cap.
  * TransferFee extension: % fee on every LODE transfer.
  * (TransferHook optional in v2+)

* **Treasury / Fee Engine – `LODE_TREASURY`**

  * Owns TransferFee withdraw authority.
  * Harvests withheld fees and splits: burn / staking rewards / lottery pot.

* **Staking Vault – `LODE_STAKING`**

  * Users stake LODE to:

    * share emissions,
    * share fee revenue,
    * gain mining/lottery eligibility.

* **Mining / Lottery Engine – `LODE_MINING`**

  * Daily epochs.
  * Calculates hashrate per staker (stake + time + paid boosts).
  * Uses VRF-based randomness to pick multiple winners.
  * Winners claim rewards from a vault (pull model).

---

## 3. Supply & Emissions

### 3.1 Supply / Allocations

Let:

* `S_max = 21,000,000 LODE` (placeholder number; can adjust)

Conceptual allocation (for feedback):

* **Presale** – 25%

  * Flat price, per-wallet cap (e.g. 5k–10k LODE) to reduce early whale concentration.
* **Team / Contributors** – 15%

  * 4-year vest (1-year cliff, 3 years linear).
* **Liquidity / MM** – 10%

  * AMM pools, market-making.
* **Emissions (“Mining Bucket”)** – 40%

  * Only emitted via `LODE_MINING`.
* **Ecosystem / Partnerships** – 10%

Implementation: either pre-mint S_max and lock emission bucket under program control or let the emission program own `mint_authority` and revoke once the bucket is emitted.

### 3.2 Emission Curve (BTC-like, 4-year halvings)

Parameters (tunable, but this is a strong starting point):

* Epoch for *emissions* can be weekly or tied to mining epoch (daily); for simplicity, assume weekly accounting.
* **Halving interval:** 4 years
  Crypto moves fast, but SoV branding benefits from patience.

Let:

* `T_epoch_emission` = 1 week
* `H` = 4 years ≈ 208 weeks
* `E0` = initial LODE emission per week

Then:

```text
epoch   = floor((t_now - t_genesis) / T_epoch_emission)
halvings= floor(epoch / H)
E(epoch)= E0 / 2^halvings
```

Subject to:

```text
Σ_epoch E(epoch) ≤ 0.40 * S_max
```

Emissions **only** go to stakers via the mining engine; non-stakers get no new LODE.

---

## 4. Global Transfer Fee

We use Token-2022 `TransferFee` on LODE:

* **Fee rate** `f_transfer`:

  * v1 proposal: **0.50%** (50 bps).
  * This is the “vault coin” view: LODE is not meant for rapid “everyday spending”; movement should be meaningful and value-accruing.
  * Callout: this is a knob; dropping to 0.25% later is possible if needed.

* **Max fee** `F_max`:

  * v1 proposal: **100 LODE** per transfer.

For any transfer of `amount` LODE:

```text
raw_fee = amount * f_transfer / 10_000
fee     = min(raw_fee, F_max)
net_to_recipient = amount - fee
```

All withheld fees accumulate under the Treasury’s `withdraw_authority` and are periodically harvested.

**Important:**
We **do not exempt staking deposits** from the transfer fee. Splitting stake across many wallets incurs many deposits → many fees, but **gives no increase in base hashrate** → Sybil is unprofitable.

---

## 5. Fee Split: Burn vs Staking vs Lottery

When `LODE_TREASURY.harvest_fees()` runs:

* Let `F_total` = total LODE fees harvested since last run.

We split:

* `α` – burn
* `β` – staking rewards
* `γ` – lottery/mining pot
  such that: `α + β + γ = 1`

**v1 recommendation:**

* `α` = 0.40 → 40% burned (global deflation)
* `β` = 0.10 → 10% to stakers as baseline yield
* `γ` = 0.50 → 50% to lottery/mining pot

Rationale:

* 40%: strengthens the “deflationary SoV” narrative.
* 10%: makes staking feel “not pointless”, but not the main attraction.
* 50%: supercharges the daily pot → more pay-to-mine → more burning.

---

## 6. Staking & Time Weighting

### 6.1 Staking

Users call `stake(amount)`:

* LODE transferred → `LODE_STAKING` vault (and pays normal transfer fee).
* Contract tracks per user:

  * `stake_i` – current staked LODE,
  * `t_stake_i` – timestamp of last stake *reset*.

Unstake:

* On full/partial unstake, user’s `stake_i` decreases.
* **Time multiplier resets to 1.0** for the unstaked portion (simple rule: any unstake resets the clock).

We may separately track `lifetime_staked_days_i` for future “loyalty perks” in v2, but v1 logic is just `stake / unstake / reset`.

### 6.2 Time Multiplier

We reward long-term commitment via a multiplier `T_i`:

Parameters:

* `T_max = 2.0` (max 2× boost from time),
* `τ = 180 days` (time to reach full multiplier).

Compute:

```text
Δt_i = t_now - t_stake_i

T_i = 1 + (T_max - 1) * min(Δt_i / τ, 1)
```

* Immediately after staking: `T_i ≈ 1.0`
* After 180 days of uninterrupted stake: `T_i = 2.0` and stays capped.

Baseline hashrate from stake:

```text
H_stake_i = stake_i * T_i
```

This is **linear** in stake, Sybil-neutral, and time-rewarding.

### 6.3 Minimum stake for mining

To avoid dust lotteries:

* Require `stake_i ≥ S_min` to be eligible for mining/lottery.
* Example: `S_min = 10 LODE` (tunable).

---

## 7. Pay-to-Mine (Proof-of-Burn Boost)

Pay-to-Mine turns **burning LODE** into **temporary hashrate**.

For epoch `e`, user `i` can call:

```text
buy_hashrate_lode(spend_lode)
```

Mechanics:

1. `spend_lode` is transferred from user → mining program.
2. Program **burns 100%** of `spend_lode` in v1 (simplest, cleanest).
3. User gets **paid hashrate** for this epoch only:

We use a concave mapping + cap:

* Diminishing returns in spend:

  ```text
  H_paid_i_raw = k_paid * sqrt(spend_lode)
  ```

* Cap relative to stake hashrate:

  ```text
  H_paid_i = min(H_paid_i_raw, m_max * H_stake_i)
  ```

**v1 recommendation:**

* `m_max = 1.0` → you can at most **double** your total hashrate via burning.

So:

```text
H_i = H_stake_i + H_paid_i
```

Properties:

* You **must stake** to benefit (if `H_stake_i = 0`, cap forces `H_paid_i = 0` even if you burn).
* You cannot infinitely pay-to-win; after some burn, your `H_paid_i` stops scaling.
* All paid mining is pure **deflation** (LODE burned).

Stable-based pay-to-mine (USDC → buy & burn LODE) is v2 scope.

---

## 8. Mining / Lottery Loop

### 8.1 Epoch Pacing

* **Mining epoch length:** `T_epoch_mining = 24 hours` (1 day).

  * Daily ritual: “check LODE, consider burning, see if you won.”

Emissions can be accounted weekly in the background; for UX, users only see the daily draw.

### 8.2 Block Reward per Epoch

For epoch `e`:

* `E_epoch` – fraction of weekly LODE emission allocated to this epoch (pro-rata).
* `L_epoch` – share of fee pool `γ * F_total` allocated since last epoch (can be in LODE and/or converted to SOL/USDC).

Total block reward:

```text
R_epoch = E_epoch + L_epoch
```

Design choice v1:

* **Jackpot-focused:** treat most of `R_epoch` as lottery payout. Staking yield (β share) is distributed separately as pro-rata LODE.

### 8.3 Winners per Epoch

To keep small stakers engaged:

* **N_winners per day:** 20–100 (tunable; good starting point ≈ 64).

Payout structure example (if 64 winners):

* Rank 1: 20% of R_epoch
* Ranks 2–10: 30% (3.33% each)
* Ranks 11–64: 50% (≈0.93% each)

This ensures:

* Whales (big H) often land in the top ranks.
* Small stakers still see their address win occasionally in the long tail.

### 8.4 Win Probability

In epoch `e`:

* Compute `H_i` for all eligible stakers.
* Let `H_total = Σ_i H_i`.
* Probability that `i` is selected as winner in a given draw:

```text
P_i = H_i / H_total
```

We draw winners using VRF randomness (see section 9).

### 8.5 Claiming Rewards (Pull Pattern)

* Winners & reward amounts are written on-chain by `LODE_MINING`.
* Rewards go into per-user “pending rewards” balances (e.g. struct in program state or SPL account).
* Users call `claim()` to pull rewards from the program vault.

Advantages:

* No mass airdrop; avoids CU and fee blow-ups.
* Winner can claim on their own schedule.

**Optional v2:**
If rewards unclaimed after N days, they can roll back into the jackpot pot (jackpot rollover / Mega Millions effect).

---

## 9. Randomness (VRF)

Because the lottery may pay out significant value, we need **manipulation-resistant randomness**.

v1 plan:

* Integrate **Switchboard VRF** or **Pyth Entropy** as randomness oracle.
* Each epoch:

  * Mining program requests randomness.
  * VRF callback writes a verified random value to the program.
  * That random seed + epoch ID + draw index are used to sample winners.

Costs:

* Each VRF request has a fee (paid in SOL or protocol tokens).
* Treasury should allocate a small budget from fee share to fund VRF.

If VRF not available early, we can start with a simpler commit–reveal scheme (e.g. using delayed blockhash) but must treat it as temporary.

---

## 10. Edge Cases & Rules

**Unstake behavior:**

* Any unstake:

  * reduces `stake_i`,
  * **resets** `t_stake_i` to `t_now` for the remaining stake,
  * so `T_i` returns to 1.0 for that position.

**Minimum stake for eligibility:**

* If `stake_i < S_min` for an epoch, `H_i = 0` (no tickets).
* User still earns pro-rata β yield if we choose to let all stakers earn it; or we can gate that too.

**Dust control:**

* Enforce `S_min` as on-chain check.
* TransferFee already makes large-scale dust spamming costly.

**Fees on staking / unstaking:**

* Deposit to staking vault:

  * Normal Token-2022 transfer → fee applies.
* Withdraw from staking vault:

  * Normal Token-2022 transfer → fee applies.

We do **not** complicate this with fee refunds in v1.

---

## 11. Parameter Table (Current Proposal)

These are the current “best guess” defaults. All are knobs for feedback.

### Supply / Emissions

* `S_max`: 21,000,000 LODE
* Emission bucket: 40% of supply
* Halving: every 4 years
* Emission epoch: 1 week

### Transfer Fee

* `f_transfer`: 0.50%
* `F_max`: 100 LODE

### Fee Split (α / β / γ)

* Burn `α`: 40%
* Stakers `β`: 10%
* Lottery `γ`: 50%

### Staking / Time

* `T_max`: 2.0
* `τ`: 180 days to reach `T_max`
* Minimum stake `S_min`: e.g. 10 LODE

### Pay-to-Mine

* Asset: LODE only in v1
* Hasrate boost:

  * `H_paid_i_raw = k_paid * sqrt(spend_lode)`
  * `H_paid_i ≤ 1.0 * H_stake_i` (max 2× total hashrate)
* Boost duration: 1 epoch (24 hours)

### Mining / Lottery

* Mining epoch: 24 hours
* Winners per epoch: 20–100 (start ~64)
* Rewards: mix of LODE emissions + SOL/USDC from fees
* Claim: pull-based `claim()` by winners

---

## 12. Naming & Brand

Working name: **LODE**

* Ticker: `LODE`
* Brand phrases:

  * “**Gamified Gold** on Solana”
  * “**Mine with your bags.** Stake and burn LODE to win daily yields.”
  * “Every move makes LODE more scarce.”

Some possible naming angles you can float:

* **Lode Protocol** – the system as a whole.
* **Motherlode** – name for the main mining contract/lottery UI.
* **Lode Vault** – staking contract / front-end.
* **Lode Rate** – dashboard that shows burn rate, remaining emissions, daily jackpots.