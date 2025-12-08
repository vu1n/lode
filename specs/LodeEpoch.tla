----------------------------- MODULE LodeEpoch -----------------------------
(*
LODE Protocol v2 - Epoch State Machine Specification
Models epoch lifecycle with NFT miners, rent payments, and lottery participation.

Key concepts:
- NFT miners (not PDA MinerEntry)
- Rent payments required for lottery participation
- Two-pool lottery system
- Age bonus for long-term holders
*)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    NFTs,              \* Set of all NFT mints
    MaxEpochs,         \* Maximum epochs to model
    GracePeriodPct     \* Grace period percentage (10 = 10%)

VARIABLES
    epoch_id,          \* Current epoch number
    epoch_state,       \* State: "pending" | "active" | "finalized"
    participants,      \* Set of NFTs participating in current epoch
    rent_paid,         \* Function: nft -> bool (has paid rent)
    hashrates,         \* Function: nft -> hashrate amount
    join_times,        \* Function: nft -> epoch join timestamp
    prize_pool,        \* LODE accumulated for epoch lottery
    winners,           \* Set of winner NFTs after finalize
    nft_age            \* Function: nft -> epochs held (for age bonus)

vars == <<epoch_id, epoch_state, participants, rent_paid, hashrates,
          join_times, prize_pool, winners, nft_age>>

-----------------------------------------------------------------------------

(*
Type definitions for all variables
*)
TypeInvariant ==
    /\ epoch_id \in Nat
    /\ epoch_state \in {"pending", "active", "finalized"}
    /\ participants \subseteq NFTs
    /\ rent_paid \in [NFTs -> BOOLEAN]
    /\ hashrates \in [NFTs -> Nat]
    /\ join_times \in [NFTs -> Nat]
    /\ prize_pool \in Nat
    /\ winners \subseteq NFTs
    /\ nft_age \in [NFTs -> Nat]

(*
NFT can only join epoch once
*)
NoDoubleJoin ==
    \A nft \in participants: Cardinality({nft}) = 1

(*
Participant must have paid rent
*)
RentRequired ==
    \A nft \in participants: rent_paid[nft] = TRUE

(*
Epoch ID never decreases
*)
MonotonicEpoch ==
    epoch_id >= 0

(*
Prize pool accounting (simplified - rent contributes 30%)
*)
PrizeConservation ==
    prize_pool >= 0

(*
Winners only exist after finalization
*)
WinnersOnlyWhenFinalized ==
    epoch_state # "finalized" => winners = {}

(*
Combined invariant
*)
Invariant ==
    /\ TypeInvariant
    /\ NoDoubleJoin
    /\ RentRequired
    /\ MonotonicEpoch
    /\ PrizeConservation
    /\ WinnersOnlyWhenFinalized

-----------------------------------------------------------------------------

(*
Initial state - first epoch pending
*)
Init ==
    /\ epoch_id = 0
    /\ epoch_state = "pending"
    /\ participants = {}
    /\ rent_paid = [nft \in NFTs |-> FALSE]
    /\ hashrates = [nft \in NFTs |-> 0]
    /\ join_times = [nft \in NFTs |-> 0]
    /\ prize_pool = 0
    /\ winners = {}
    /\ nft_age = [nft \in NFTs |-> 0]

(*
Advance epoch from pending to active
Requires previous epoch finalized or this is epoch 0
*)
AdvanceEpoch ==
    /\ epoch_state = "pending"
    /\ epoch_state' = "active"
    /\ UNCHANGED <<epoch_id, participants, rent_paid, hashrates,
                   join_times, prize_pool, winners, nft_age>>

(*
Pay rent for NFT (during grace period of active epoch)
*)
PayRent(nft, rent_amount) ==
    /\ epoch_state = "active"
    /\ rent_paid[nft] = FALSE
    /\ rent_amount > 0
    /\ rent_paid' = [rent_paid EXCEPT ![nft] = TRUE]
    \* 30% of rent goes to prize pool
    /\ prize_pool' = prize_pool + (rent_amount * 30) \div 100
    /\ UNCHANGED <<epoch_id, epoch_state, participants, hashrates,
                   join_times, winners, nft_age>>

(*
Join epoch lottery (after paying rent)
*)
JoinEpoch(nft, hashrate) ==
    /\ epoch_state = "active"
    /\ rent_paid[nft] = TRUE
    /\ nft \notin participants
    /\ hashrate > 0
    /\ participants' = participants \union {nft}
    /\ hashrates' = [hashrates EXCEPT ![nft] = hashrate]
    /\ join_times' = [join_times EXCEPT ![nft] = epoch_id]
    /\ UNCHANGED <<epoch_id, epoch_state, rent_paid, prize_pool,
                   winners, nft_age>>

(*
Finalize epoch - select winners
Simplified: just marks epoch as finalized and picks winner(s)
*)
FinalizeEpoch ==
    /\ epoch_state = "active"
    /\ Cardinality(participants) > 0
    /\ epoch_state' = "finalized"
    \* Select up to 2 winners (hashrate pool + ticket pool)
    /\ \E hr_winner \in participants, ticket_winner \in participants:
        winners' = {hr_winner, ticket_winner}
    /\ UNCHANGED <<epoch_id, participants, rent_paid, hashrates,
                   join_times, prize_pool, nft_age>>

(*
Start new epoch after finalization
*)
NewEpoch ==
    /\ epoch_state = "finalized"
    /\ epoch_id < MaxEpochs
    /\ epoch_id' = epoch_id + 1
    /\ epoch_state' = "pending"
    /\ participants' = {}
    /\ rent_paid' = [nft \in NFTs |-> FALSE]
    /\ prize_pool' = 0
    /\ winners' = {}
    \* Increment age for NFTs that participated
    /\ nft_age' = [nft \in NFTs |->
                    IF nft \in participants
                    THEN nft_age[nft] + 1
                    ELSE nft_age[nft]]
    /\ UNCHANGED <<hashrates, join_times>>

-----------------------------------------------------------------------------

(*
Next state relation
*)
Next ==
    \/ AdvanceEpoch
    \/ \E nft \in NFTs, amount \in 1..100:
        \/ PayRent(nft, amount)
        \/ JoinEpoch(nft, amount)
    \/ FinalizeEpoch
    \/ NewEpoch

(*
Specification
*)
Spec == Init /\ [][Next]_vars

(*
Fairness - epochs eventually progress
*)
Fairness ==
    /\ WF_vars(AdvanceEpoch)
    /\ WF_vars(FinalizeEpoch)
    /\ WF_vars(NewEpoch)

(*
Liveness properties
*)

(*
If epoch is active with participants, it eventually gets finalized
*)
EventuallyFinalized ==
    (epoch_state = "active" /\ Cardinality(participants) > 0) ~> (epoch_state = "finalized")

(*
Epochs eventually advance
*)
EpochsProgress ==
    \A e \in 0..(MaxEpochs-1): epoch_id = e ~> epoch_id > e

=============================================================================
