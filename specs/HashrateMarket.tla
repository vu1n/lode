--------------------------- MODULE HashrateMarket ---------------------------
(*
LODE Hashrate Marketplace Specification
Models the hashrate marketplace where users can list and buy hashrate.
Key properties:
- Only booted hashrate can be listed
- Market purchases are instantly booted
- Locked hashrate matches active listings
*)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    Users,              \* Set of all users
    MaxListingId        \* Maximum listing ID for model checking bounds

VARIABLES
    listings,           \* Sequence of active listings
    lockedHashrate,     \* Function: user -> amount of hashrate locked in listings
    bookedHashrate,     \* Function: user -> permanently booked hashrate
    bootingHashrate,    \* Function: user -> hashrate in booting period
    nextListingId       \* Next available listing ID

vars == <<listings, lockedHashrate, bookedHashrate, bootingHashrate, nextListingId>>

-----------------------------------------------------------------------------

(*
Listing record structure
*)
Listing == [
    id: Nat,           \* Unique listing ID
    seller: Users,     \* User who listed the hashrate
    amount: Nat,       \* Amount of hashrate for sale
    price: Nat         \* Price per unit (in tokens)
]

(*
Type definitions
*)
TypeInvariant ==
    /\ listings \in Seq(Listing)
    /\ lockedHashrate \in [Users -> Nat]
    /\ bookedHashrate \in [Users -> Nat]
    /\ bootingHashrate \in [Users -> Nat]
    /\ nextListingId \in Nat

(*
Sum of listing amounts for a user must equal their locked hashrate
*)
LockedMatchesListings ==
    \A user \in Users:
        LET userListings == {l \in DOMAIN listings: listings[l].seller = user}
            totalListed == IF userListings = {}
                          THEN 0
                          ELSE LET Sum[S \in SUBSET userListings] ==
                                   IF S = {}
                                   THEN 0
                                   ELSE LET x == CHOOSE x \in S: TRUE
                                        IN listings[x].amount + Sum[S \ {x}]
                               IN Sum[userListings]
        IN lockedHashrate[user] = totalListed

(*
Users can only list hashrate they have booted (not booting)
booked >= locked
*)
OnlyBootedSellable ==
    \A user \in Users:
        bookedHashrate[user] >= lockedHashrate[user]

(*
Market-bought hashrate is immediately booted (not in booting period)
This is enforced by the MarketBuyHashrate action
*)
MarketBuyInstant ==
    TRUE  \* Property enforced by action, not state invariant

(*
No negative balances
*)
NoNegativeBalances ==
    /\ \A user \in Users: bookedHashrate[user] >= 0
    /\ \A user \in Users: bootingHashrate[user] >= 0
    /\ \A user \in Users: lockedHashrate[user] >= 0

(*
All listing IDs are unique
*)
UniqueListingIds ==
    \A i, j \in DOMAIN listings:
        i # j => listings[i].id # listings[j].id

(*
Combined invariant
*)
Invariant ==
    /\ TypeInvariant
    /\ LockedMatchesListings
    /\ OnlyBootedSellable
    /\ NoNegativeBalances
    /\ UniqueListingIds

-----------------------------------------------------------------------------

(*
Initial state
*)
Init ==
    /\ listings = <<>>
    /\ lockedHashrate = [user \in Users |-> 0]
    /\ bookedHashrate = [user \in Users |-> 0]
    /\ bootingHashrate = [user \in Users |-> 0]
    /\ nextListingId = 1

(*
User lists hashrate for sale
*)
ListHashrate(seller, amount, price) ==
    /\ amount > 0
    /\ price > 0
    /\ nextListingId <= MaxListingId  \* Bound for model checking
    /\ bookedHashrate[seller] >= lockedHashrate[seller] + amount  \* Has available booted hashrate
    /\ LET newListing == [
           id |-> nextListingId,
           seller |-> seller,
           amount |-> amount,
           price |-> price
       ]
       IN /\ listings' = Append(listings, newListing)
          /\ lockedHashrate' = [lockedHashrate EXCEPT ![seller] = @ + amount]
          /\ nextListingId' = nextListingId + 1
    /\ UNCHANGED <<bookedHashrate, bootingHashrate>>

(*
User buys hashrate from a listing
Hashrate is instantly booted for buyer
*)
BuyListedHashrate(buyer, listingIdx) ==
    /\ listingIdx \in DOMAIN listings
    /\ LET listing == listings[listingIdx]
           seller == listing.seller
           amount == listing.amount
       IN /\ seller # buyer  \* Cannot buy own listing
          /\ bookedHashrate' = [bookedHashrate EXCEPT
                                 ![buyer] = @ + amount,
                                 ![seller] = @ - amount]
          /\ lockedHashrate' = [lockedHashrate EXCEPT ![seller] = @ - amount]
          /\ listings' = [i \in DOMAIN listings |->
                          IF i < listingIdx
                          THEN listings[i]
                          ELSE IF i = listingIdx
                               THEN listings[Len(listings)]
                               ELSE listings[i]] \* Remove by swapping with last
          /\ IF Len(listings) > 1
             THEN listings' = SubSeq(listings', 1, Len(listings) - 1)
             ELSE listings' = <<>>
    /\ UNCHANGED <<bootingHashrate, nextListingId>>

(*
Simplified version: just remove the listing
*)
BuyListedHashrateSimple(buyer, listingIdx) ==
    /\ listingIdx \in DOMAIN listings
    /\ LET listing == listings[listingIdx]
           seller == listing.seller
           amount == listing.amount
       IN /\ seller # buyer
          /\ bookedHashrate' = [bookedHashrate EXCEPT
                                 ![buyer] = @ + amount,
                                 ![seller] = @ - amount]
          /\ lockedHashrate' = [lockedHashrate EXCEPT ![seller] = @ - amount]
          /\ listings' = SelectSeq(listings, LAMBDA l: l.id # listing.id)
          /\ UNCHANGED <<bootingHashrate, nextListingId>>

(*
User cancels their own listing
*)
CancelListing(seller, listingIdx) ==
    /\ listingIdx \in DOMAIN listings
    /\ LET listing == listings[listingIdx]
       IN /\ listing.seller = seller
          /\ lockedHashrate' = [lockedHashrate EXCEPT ![seller] = @ - listing.amount]
          /\ listings' = SelectSeq(listings, LAMBDA l: l.id # listing.id)
    /\ UNCHANGED <<bookedHashrate, bootingHashrate, nextListingId>>

(*
Complete a booting period (hashrate moves from booting to booked)
This simulates the passage of time
*)
CompleteBooting(user) ==
    /\ bootingHashrate[user] > 0
    /\ bookedHashrate' = [bookedHashrate EXCEPT ![user] = @ + bootingHashrate[user]]
    /\ bootingHashrate' = [bootingHashrate EXCEPT ![user] = 0]
    /\ UNCHANGED <<listings, lockedHashrate, nextListingId>>

(*
User purchases hashrate directly (enters booting)
Not from marketplace, starts booting period
*)
DirectBuyHashrate(user, amount) ==
    /\ amount > 0
    /\ bootingHashrate' = [bootingHashrate EXCEPT ![user] = @ + amount]
    /\ UNCHANGED <<listings, lockedHashrate, bookedHashrate, nextListingId>>

-----------------------------------------------------------------------------

(*
Next state relation
*)
Next ==
    \/ \E seller \in Users, amount \in Nat, price \in Nat:
        ListHashrate(seller, amount, price)
    \/ \E buyer \in Users, idx \in DOMAIN listings:
        BuyListedHashrateSimple(buyer, idx)
    \/ \E seller \in Users, idx \in DOMAIN listings:
        CancelListing(seller, idx)
    \/ \E user \in Users:
        CompleteBooting(user)
    \/ \E user \in Users, amount \in Nat:
        DirectBuyHashrate(user, amount)

(*
Specification
*)
Spec == Init /\ [][Next]_vars

(*
Temporal properties
*)

(*
Listings eventually get fulfilled or cancelled
*)
ListingsEventuallyResolved ==
    \A l \in DOMAIN listings:
        <>(l \notin DOMAIN listings)

(*
Fairness properties
*)
Fairness ==
    /\ WF_vars(\E user \in Users: CompleteBooting(user))
    /\ SF_vars(\E buyer \in Users, idx \in DOMAIN listings: BuyListedHashrateSimple(buyer, idx))

=============================================================================
