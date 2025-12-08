---------------------------- MODULE LodeEmissions ----------------------------
(*
LODE Emission Schedule Specification
Models the emission schedule with halving phases and tail emission.
- First 8 years: Halving schedule (40% of max supply)
- After year 8: Tail emission at 30 bps daily
*)

EXTENDS Integers, Sequences, TLC

CONSTANTS
    MAX_SUPPLY,           \* Maximum supply cap (210M)
    TAIL_EMISSION_BPS,    \* Tail emission rate in basis points (30)
    HALVING_INTERVAL,     \* Epochs between halvings (52 weeks)
    INITIAL_SUPPLY        \* Starting supply

VARIABLES
    currentWeek,          \* Current week number
    totalEmitted,         \* Total tokens emitted so far
    currentSupply,        \* Current circulating supply
    halvingPhase          \* Current halving phase (0-7, or 8+ for tail)

vars == <<currentWeek, totalEmitted, currentSupply, halvingPhase>>

-----------------------------------------------------------------------------

(*
Constants for emission calculation
*)
HALVING_PHASES == 8                              \* 8 halving phases
HALVING_EMISSION_CAP == MAX_SUPPLY * 40 \div 100 \* 40% of max supply
WEEKS_PER_YEAR == 52
TAIL_START_WEEK == WEEKS_PER_YEAR * 8            \* Week 416

(*
Type definitions
*)
TypeInvariant ==
    /\ currentWeek \in Nat
    /\ totalEmitted \in Nat
    /\ currentSupply \in Nat
    /\ halvingPhase \in Nat

(*
During halving phase (first 8 years), total emissions cannot exceed 40% of max supply
*)
EmissionCap ==
    currentWeek < TAIL_START_WEEK => totalEmitted <= HALVING_EMISSION_CAP

(*
After year 8, emission rate must follow tail emission formula
Daily emission = (current_supply * 30 / 10000) / 365
Weekly emission = daily * 7
*)
TailEmissionRate ==
    LET dailyEmission == (currentSupply * TAIL_EMISSION_BPS) \div 10000 \div 365
        weeklyEmission == dailyEmission * 7
    IN currentWeek >= TAIL_START_WEEK => weeklyEmission > 0

(*
Supply must never exceed max supply
*)
SupplyCap ==
    currentSupply <= MAX_SUPPLY

(*
Total emitted must be consistent with current supply
*)
SupplyConsistency ==
    currentSupply = INITIAL_SUPPLY + totalEmitted

(*
Combined invariant
*)
Invariant ==
    /\ TypeInvariant
    /\ EmissionCap
    /\ TailEmissionRate
    /\ SupplyCap
    /\ SupplyConsistency

-----------------------------------------------------------------------------

(*
Calculate halving phase from week number
Phase 0: weeks 0-51, Phase 1: weeks 52-103, etc.
*)
GetHalvingPhase(week) ==
    IF week >= TAIL_START_WEEK
    THEN HALVING_PHASES
    ELSE week \div HALVING_INTERVAL

(*
Calculate base emission for a given halving phase
Initial emission halves each phase
*)
GetPhaseEmission(phase) ==
    IF phase >= HALVING_PHASES
    THEN 0  \* No base emission during tail phase
    ELSE LET baseEmission == HALVING_EMISSION_CAP \div HALVING_INTERVAL
         IN baseEmission \div (2^phase)

(*
Calculate tail emission based on current supply
Daily emission = (supply * 30 bps) / 365
Weekly emission = daily * 7
*)
GetTailEmission(supply) ==
    LET dailyEmission == (supply * TAIL_EMISSION_BPS) \div 10000 \div 365
    IN dailyEmission * 7

(*
Initial state
*)
Init ==
    /\ currentWeek = 0
    /\ totalEmitted = 0
    /\ currentSupply = INITIAL_SUPPLY
    /\ halvingPhase = 0

(*
Advance to next epoch and mint appropriate emission
*)
AdvanceEpoch ==
    /\ currentWeek' = currentWeek + 1
    /\ halvingPhase' = GetHalvingPhase(currentWeek')
    /\ LET emission ==
           IF currentWeek' < TAIL_START_WEEK
           THEN GetPhaseEmission(halvingPhase')
           ELSE GetTailEmission(currentSupply)
       IN /\ totalEmitted' = totalEmitted + emission
          /\ currentSupply' = currentSupply + emission

(*
Mint emission for current epoch
Separates emission calculation from epoch advancement for clarity
*)
MintEmission ==
    LET emission ==
        IF currentWeek < TAIL_START_WEEK
        THEN GetPhaseEmission(halvingPhase)
        ELSE GetTailEmission(currentSupply)
    IN /\ emission > 0
       /\ totalEmitted' = totalEmitted + emission
       /\ currentSupply' = currentSupply + emission
       /\ UNCHANGED <<currentWeek, halvingPhase>>

-----------------------------------------------------------------------------

(*
Next state relation
*)
Next ==
    \/ AdvanceEpoch
    \/ MintEmission

(*
Specification
*)
Spec == Init /\ [][Next]_vars

(*
Temporal properties
*)

(*
Emissions eventually stop growing beyond cap
*)
EmissionsEventuallyStable ==
    <>[](totalEmitted <= HALVING_EMISSION_CAP \/ currentWeek >= TAIL_START_WEEK)

(*
Halving phases advance
*)
HalvingProgression ==
    \A phase \in 0..(HALVING_PHASES-1):
        currentWeek >= phase * HALVING_INTERVAL => halvingPhase >= phase

(*
Fairness: epochs must eventually advance
*)
Fairness ==
    WF_vars(AdvanceEpoch)

=============================================================================
