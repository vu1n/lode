----------------------------- MODULE LodeMining -----------------------------
(*
Core LODE Mining Protocol Specification
Models the core mining/lottery invariants including staking, hashrate booking,
and supply conservation.
*)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    Users,              \* Set of all users
    InitialSupply,      \* Initial token supply
    MaxHashratePerToken \* Maximum hashrate per staked token

VARIABLES
    supply,             \* Current circulating supply
    totalEmitted,       \* Total tokens emitted through mining
    totalBurned,        \* Total tokens burned
    epoch,              \* Current epoch number
    stakes,             \* Function: user -> staked amount
    bookedHashrate,     \* Function: user -> permanently booked hashrate
    bootingHashrate     \* Function: user -> hashrate in booting period

vars == <<supply, totalEmitted, totalBurned, epoch, stakes, bookedHashrate, bootingHashrate>>

-----------------------------------------------------------------------------

(*
Type definitions for all variables
*)
TypeInvariant ==
    /\ supply \in Nat
    /\ totalEmitted \in Nat
    /\ totalBurned \in Nat
    /\ epoch \in Nat
    /\ stakes \in [Users -> Nat]
    /\ bookedHashrate \in [Users -> Nat]
    /\ bootingHashrate \in [Users -> Nat]

(*
Supply must equal initial supply plus emissions minus burns
*)
SupplyConservation ==
    supply = InitialSupply + totalEmitted - totalBurned

(*
Total permanent hashrate cannot exceed stake-derived hashrate
For each user, booked + booting hashrate <= stake * MaxHashratePerToken
*)
HashrateCap ==
    \A user \in Users:
        bookedHashrate[user] + bootingHashrate[user] <= stakes[user] * MaxHashratePerToken

(*
No user can have negative balances
*)
NoNegativeBalances ==
    /\ \A user \in Users: stakes[user] >= 0
    /\ \A user \in Users: bookedHashrate[user] >= 0
    /\ \A user \in Users: bootingHashrate[user] >= 0

(*
Combined invariant
*)
Invariant ==
    /\ TypeInvariant
    /\ SupplyConservation
    /\ HashrateCap
    /\ NoNegativeBalances

-----------------------------------------------------------------------------

(*
Initial state
*)
Init ==
    /\ supply = InitialSupply
    /\ totalEmitted = 0
    /\ totalBurned = 0
    /\ epoch = 0
    /\ stakes = [user \in Users |-> 0]
    /\ bookedHashrate = [user \in Users |-> 0]
    /\ bootingHashrate = [user \in Users |-> 0]

(*
User stakes tokens
*)
Stake(user, amount) ==
    /\ amount > 0
    /\ supply >= amount  \* Must have sufficient supply (user has tokens)
    /\ stakes' = [stakes EXCEPT ![user] = @ + amount]
    /\ UNCHANGED <<supply, totalEmitted, totalBurned, epoch, bookedHashrate, bootingHashrate>>

(*
User unstakes tokens
Requires: booked + booting hashrate must be reduced proportionally or removed first
*)
Unstake(user, amount) ==
    /\ amount > 0
    /\ stakes[user] >= amount
    /\ LET newStake == stakes[user] - amount
           maxHashrate == newStake * MaxHashratePerToken
       IN bookedHashrate[user] + bootingHashrate[user] <= maxHashrate
    /\ stakes' = [stakes EXCEPT ![user] = @ - amount]
    /\ UNCHANGED <<supply, totalEmitted, totalBurned, epoch, bookedHashrate, bootingHashrate>>

(*
User buys hashrate (enters booting period)
Requires sufficient stake to support new hashrate
*)
BuyHashrate(user, amount) ==
    /\ amount > 0
    /\ LET maxHashrate == stakes[user] * MaxHashratePerToken
           currentHashrate == bookedHashrate[user] + bootingHashrate[user]
       IN currentHashrate + amount <= maxHashrate
    /\ bootingHashrate' = [bootingHashrate EXCEPT ![user] = @ + amount]
    /\ UNCHANGED <<supply, totalEmitted, totalBurned, epoch, stakes, bookedHashrate>>

(*
User buys hashrate from market (instant boot)
Market purchases bypass booting period
*)
MarketBuyHashrate(user, amount) ==
    /\ amount > 0
    /\ LET maxHashrate == stakes[user] * MaxHashratePerToken
           currentHashrate == bookedHashrate[user] + bootingHashrate[user]
       IN currentHashrate + amount <= maxHashrate
    /\ bookedHashrate' = [bookedHashrate EXCEPT ![user] = @ + amount]
    /\ UNCHANGED <<supply, totalEmitted, totalBurned, epoch, stakes, bootingHashrate>>

(*
User sells hashrate
Can only sell booted (permanent) hashrate
*)
SellHashrate(user, amount) ==
    /\ amount > 0
    /\ bookedHashrate[user] >= amount
    /\ bookedHashrate' = [bookedHashrate EXCEPT ![user] = @ - amount]
    /\ UNCHANGED <<supply, totalEmitted, totalBurned, epoch, stakes, bootingHashrate>>

(*
Advance epoch (booting hashrate becomes permanent)
*)
AdvanceEpoch ==
    /\ epoch' = epoch + 1
    /\ bookedHashrate' = [user \in Users |->
                           bookedHashrate[user] + bootingHashrate[user]]
    /\ bootingHashrate' = [user \in Users |-> 0]
    /\ UNCHANGED <<supply, totalEmitted, totalBurned, stakes>>

-----------------------------------------------------------------------------

(*
Next state relation
*)
Next ==
    \/ \E user \in Users, amount \in Nat:
        \/ Stake(user, amount)
        \/ Unstake(user, amount)
        \/ BuyHashrate(user, amount)
        \/ MarketBuyHashrate(user, amount)
        \/ SellHashrate(user, amount)
    \/ AdvanceEpoch

(*
Specification
*)
Spec == Init /\ [][Next]_vars

(*
Fairness properties
*)
Fairness ==
    /\ WF_vars(AdvanceEpoch)  \* Epochs eventually advance

=============================================================================
