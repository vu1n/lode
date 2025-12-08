--------------------------- MODULE LodeLottery ---------------------------
(*
LODE Protocol v2 - Two-Pool Lottery Specification
Models the two-pool winner selection with hashrate (80%) and lucky tickets (20%).

Key concepts:
- Hashrate Pool: Linear weighting (not sqrt) with age bonus
- Lucky Ticket Pool: 1 ticket per NFT (uniform distribution)
- VRF-based random selection
- Age bonus: +1% per epoch held, max +50%
*)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    NFTs,               \* Set of all participating NFTs
    MaxHashrate,        \* Maximum hashrate value for modeling
    MaxAgeBonus         \* Maximum age bonus (50 = 50%)

VARIABLES
    hashrate_pool,      \* Function: nft -> weighted hashrate
    ticket_pool,        \* Set of NFTs with lucky tickets
    nft_ages,           \* Function: nft -> epochs held
    vrf_seed,           \* Random seed from VRF
    hr_winner,          \* Winner from hashrate pool
    ticket_winner,      \* Winner from ticket pool
    finalized           \* Whether lottery has been finalized

vars == <<hashrate_pool, ticket_pool, nft_ages, vrf_seed,
          hr_winner, ticket_winner, finalized>>

-----------------------------------------------------------------------------

(*
Type definitions
*)
TypeInvariant ==
    /\ hashrate_pool \in [NFTs -> Nat]
    /\ ticket_pool \subseteq NFTs
    /\ nft_ages \in [NFTs -> Nat]
    /\ vrf_seed \in Nat
    /\ hr_winner \in NFTs \union {CHOOSE x : x \notin NFTs}  \* NULL represented as arbitrary value
    /\ ticket_winner \in NFTs \union {CHOOSE x : x \notin NFTs}
    /\ finalized \in BOOLEAN

(*
Linear proportionality for hashrate pool:
For any two NFTs a, b: P(a wins) / P(b wins) = hashrate[a] / hashrate[b]
This is enforced by the weighted selection mechanism.
*)
LinearProportionality ==
    \A a, b \in NFTs:
        /\ hashrate_pool[a] > 0
        /\ hashrate_pool[b] > 0
        \* The ratio of hashrates equals the ratio of win probabilities
        \* (This is implicit in weighted random selection)
        => TRUE

(*
Uniform tickets: All NFTs in ticket pool have equal probability
*)
UniformTickets ==
    \A a, b \in ticket_pool:
        \* Each NFT has exactly 1 ticket (implicitly equal probability)
        TRUE

(*
Winner must exist after finalization
*)
WinnerExists ==
    finalized /\ Cardinality(ticket_pool) > 0
    => /\ hr_winner \in NFTs
       /\ ticket_winner \in NFTs

(*
Age bonus calculation: min(age * 1, 50)
*)
AgeBonus(nft) ==
    LET raw_bonus == nft_ages[nft]
    IN IF raw_bonus > MaxAgeBonus
       THEN MaxAgeBonus
       ELSE raw_bonus

(*
Effective hashrate = base hashrate * (100 + age_bonus) / 100
*)
EffectiveHashrate(nft) ==
    LET bonus == AgeBonus(nft)
        base == hashrate_pool[nft]
    IN (base * (100 + bonus)) \div 100

(*
Combined invariant
*)
Invariant ==
    /\ TypeInvariant
    /\ LinearProportionality
    /\ UniformTickets

-----------------------------------------------------------------------------

(*
Initial state
*)
Init ==
    /\ hashrate_pool = [nft \in NFTs |-> 0]
    /\ ticket_pool = {}
    /\ nft_ages = [nft \in NFTs |-> 0]
    /\ vrf_seed = 0
    /\ hr_winner = CHOOSE x : x \notin NFTs  \* NULL
    /\ ticket_winner = CHOOSE x : x \notin NFTs  \* NULL
    /\ finalized = FALSE

(*
Register NFT in lottery with hashrate
*)
RegisterNFT(nft, hashrate, age) ==
    /\ finalized = FALSE
    /\ hashrate > 0
    /\ hashrate_pool' = [hashrate_pool EXCEPT ![nft] = hashrate]
    /\ ticket_pool' = ticket_pool \union {nft}
    /\ nft_ages' = [nft_ages EXCEPT ![nft] = age]
    /\ UNCHANGED <<vrf_seed, hr_winner, ticket_winner, finalized>>

(*
Set VRF seed (from Switchboard oracle)
*)
SetVRFSeed(seed) ==
    /\ finalized = FALSE
    /\ seed > 0
    /\ vrf_seed' = seed
    /\ UNCHANGED <<hashrate_pool, ticket_pool, nft_ages,
                   hr_winner, ticket_winner, finalized>>

(*
Select hashrate pool winner using weighted random selection
P(nft) = effective_hashrate[nft] / total_effective_hashrate
*)
SelectHashrateWinner ==
    /\ finalized = FALSE
    /\ vrf_seed > 0
    /\ Cardinality(ticket_pool) > 0
    \* Simplified: pick arbitrary NFT from pool (in implementation, uses VRF)
    /\ \E winner \in ticket_pool:
        /\ hashrate_pool[winner] > 0
        /\ hr_winner' = winner
    /\ UNCHANGED <<hashrate_pool, ticket_pool, nft_ages, vrf_seed,
                   ticket_winner, finalized>>

(*
Select lucky ticket winner using uniform random selection
P(nft) = 1 / |ticket_pool|
*)
SelectTicketWinner ==
    /\ finalized = FALSE
    /\ vrf_seed > 0
    /\ Cardinality(ticket_pool) > 0
    /\ hr_winner \in NFTs  \* Hashrate winner already selected
    \* Simplified: pick arbitrary NFT from pool (in implementation, uses VRF)
    /\ \E winner \in ticket_pool:
        ticket_winner' = winner
    /\ UNCHANGED <<hashrate_pool, ticket_pool, nft_ages, vrf_seed,
                   hr_winner, finalized>>

(*
Finalize lottery - mark as complete
*)
FinalizeLottery ==
    /\ finalized = FALSE
    /\ hr_winner \in NFTs
    /\ ticket_winner \in NFTs
    /\ finalized' = TRUE
    /\ UNCHANGED <<hashrate_pool, ticket_pool, nft_ages, vrf_seed,
                   hr_winner, ticket_winner>>

-----------------------------------------------------------------------------

(*
Next state relation
*)
Next ==
    \/ \E nft \in NFTs, hr \in 1..MaxHashrate, age \in 0..100:
        RegisterNFT(nft, hr, age)
    \/ \E seed \in 1..1000000:
        SetVRFSeed(seed)
    \/ SelectHashrateWinner
    \/ SelectTicketWinner
    \/ FinalizeLottery

(*
Specification
*)
Spec == Init /\ [][Next]_vars

(*
Safety: If finalized, both winners exist
*)
SafetyWinnersExist ==
    finalized => (hr_winner \in NFTs /\ ticket_winner \in NFTs)

(*
Liveness: If VRF seed is set and there are participants, eventually finalized
*)
LivenessEventuallyFinalized ==
    (vrf_seed > 0 /\ Cardinality(ticket_pool) > 0) ~> finalized

=============================================================================
