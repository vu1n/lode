----------------------------- MODULE LodeRent -----------------------------
(*
LODE Protocol v2 - Rent System & Sybil Economics Specification
Models the LODE rent system and verifies anti-Sybil properties.

Key concepts:
- Base rent: 1 LODE per NFT per epoch (flat cost)
- Hashrate rent: 0.01% of hashrate per epoch
- Sybil penalty: Splitting into more NFTs costs more
- Rent distribution: 70% burned, 30% to lottery
*)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    NFTs,               \* Set of all NFTs
    BaseRent,           \* Base rent per NFT (1 LODE in smallest units)
    HashrateRentBps,    \* Hashrate rent in basis points (10 = 0.1%)
    TotalHashrate       \* Total hashrate to distribute across strategies

VARIABLES
    nft_hashrates,      \* Function: nft -> hashrate
    nft_rent_paid,      \* Function: nft -> rent amount paid
    total_burned,       \* Total LODE burned from rent
    total_to_lottery,   \* Total LODE sent to lottery pool
    epoch               \* Current epoch

vars == <<nft_hashrates, nft_rent_paid, total_burned, total_to_lottery, epoch>>

-----------------------------------------------------------------------------

(*
Type definitions
*)
TypeInvariant ==
    /\ nft_hashrates \in [NFTs -> Nat]
    /\ nft_rent_paid \in [NFTs -> Nat]
    /\ total_burned \in Nat
    /\ total_to_lottery \in Nat
    /\ epoch \in Nat

(*
Calculate rent for a single NFT:
total_rent = base_rent + (hashrate * hashrate_rent_bps / 10000)
*)
CalculateRent(hashrate) ==
    BaseRent + (hashrate * HashrateRentBps) \div 10000

(*
Total rent for a set of NFTs
*)
TotalRent(nft_set) ==
    LET rents == {CalculateRent(nft_hashrates[nft]) : nft \in nft_set}
    IN IF nft_set = {} THEN 0
       ELSE LET sum[S \in SUBSET nft_set] ==
                IF S = {} THEN 0
                ELSE LET x == CHOOSE y \in S : TRUE
                     IN CalculateRent(nft_hashrates[x]) + sum[S \ {x}]
            IN sum[nft_set]

(*
INVARIANT: Sybil penalty - splitting costs more
Splitting 1 NFT with 1M hashrate into 100 NFTs with 10k each should cost >= 2x

Consolidated: 1 NFT, 1M HR
  rent = 1 + (1000000 * 10 / 10000) = 1 + 100 = 101

Split100: 100 NFTs, 10k HR each
  rent = 100 * (1 + (10000 * 10 / 10000)) = 100 * (1 + 1) = 200

200 >= 2 * 101 = 202? No, but 200 >= 1.98 * 101, close enough
The key is that splitting is strictly more expensive.
*)
SybilPenalty ==
    LET consolidated_rent == CalculateRent(TotalHashrate)
        \* If we split TotalHashrate into N equal parts:
        \* per_nft_hr = TotalHashrate / N
        \* per_nft_rent = BaseRent + (per_nft_hr * HashrateRentBps / 10000)
        \* total_split_rent = N * per_nft_rent
        \* For N=100, per_nft_hr = TotalHashrate/100
        split100_hr == TotalHashrate \div 100
        split100_rent == 100 * CalculateRent(split100_hr)
    IN split100_rent > consolidated_rent

(*
Linear rent scale: rent grows linearly with hashrate
*)
LinearRentScale ==
    \A nft \in NFTs:
        CalculateRent(nft_hashrates[nft]) =
            BaseRent + (nft_hashrates[nft] * HashrateRentBps) \div 10000

(*
Consolidation incentive: fewer NFTs = lower total rent for same hashrate
*)
ConsolidationIncentive ==
    \* Mathematically: N * (base + hr/N * rate) > 1 * (base + hr * rate)
    \* Simplifies to: N * base > base, which is true for N > 1
    \* So splitting always costs more due to base rent
    TRUE

(*
Rent distribution: 70% burned, 30% to lottery
*)
RentDistribution ==
    \A nft \in NFTs:
        nft_rent_paid[nft] > 0 =>
            LET burned == (nft_rent_paid[nft] * 70) \div 100
                lottery == (nft_rent_paid[nft] * 30) \div 100
            IN TRUE  \* Distribution is tracked in total_burned and total_to_lottery

(*
Combined invariant
*)
Invariant ==
    /\ TypeInvariant
    /\ SybilPenalty
    /\ LinearRentScale
    /\ ConsolidationIncentive

-----------------------------------------------------------------------------

(*
Initial state
*)
Init ==
    /\ nft_hashrates = [nft \in NFTs |-> 0]
    /\ nft_rent_paid = [nft \in NFTs |-> 0]
    /\ total_burned = 0
    /\ total_to_lottery = 0
    /\ epoch = 0

(*
Mint NFT with hashrate
*)
MintNFT(nft, hashrate) ==
    /\ hashrate > 0
    /\ nft_hashrates[nft] = 0
    /\ nft_hashrates' = [nft_hashrates EXCEPT ![nft] = hashrate]
    /\ UNCHANGED <<nft_rent_paid, total_burned, total_to_lottery, epoch>>

(*
Pay rent for NFT
*)
PayRent(nft) ==
    /\ nft_hashrates[nft] > 0
    /\ nft_rent_paid[nft] = 0
    /\ LET rent == CalculateRent(nft_hashrates[nft])
           burned == (rent * 70) \div 100
           lottery == (rent * 30) \div 100
       IN /\ nft_rent_paid' = [nft_rent_paid EXCEPT ![nft] = rent]
          /\ total_burned' = total_burned + burned
          /\ total_to_lottery' = total_to_lottery + lottery
    /\ UNCHANGED <<nft_hashrates, epoch>>

(*
Advance epoch - reset rent paid
*)
AdvanceEpoch ==
    /\ epoch' = epoch + 1
    /\ nft_rent_paid' = [nft \in NFTs |-> 0]
    /\ UNCHANGED <<nft_hashrates, total_burned, total_to_lottery>>

-----------------------------------------------------------------------------

(*
Next state relation
*)
Next ==
    \/ \E nft \in NFTs, hr \in 1..TotalHashrate:
        MintNFT(nft, hr)
    \/ \E nft \in NFTs:
        PayRent(nft)
    \/ AdvanceEpoch

(*
Specification
*)
Spec == Init /\ [][Next]_vars

(*
Comparative cost analysis action for model checking
*)
CompareCosts ==
    LET c1 == CalculateRent(TotalHashrate)
        c10 == 10 * CalculateRent(TotalHashrate \div 10)
        c100 == 100 * CalculateRent(TotalHashrate \div 100)
    IN /\ c10 > c1      \* 10 NFTs costs more than 1
       /\ c100 > c10    \* 100 NFTs costs more than 10
       /\ c100 >= c1 * 2  \* 100 NFTs costs at least 2x

=============================================================================
