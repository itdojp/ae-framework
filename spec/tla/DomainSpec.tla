------------------------------ MODULE DomainSpec ------------------------------
EXTENDS Naturals, Sequences

(* Minimal skeleton for illustration. Replace with domain-specific spec. *)

VARIABLES state

Init == state = [ onHand |-> 0, allocated |-> 0 ]

Next == 
  \/ \E qty \in Nat : qty > 0 /\ state' = [state EXCEPT !.onHand = @ + qty]
  \/ \E qty \in Nat : qty > 0 /\ state.allocated + qty <= state.onHand /\ state' = [state EXCEPT !.allocated = @ + qty]
  \/ \E qty \in Nat : qty > 0 /\ qty <= state.allocated /\ state' = [state EXCEPT !.allocated = @ - qty, !.onHand = @ - qty]

Invariant == state.onHand \geq 0 /\ state.allocated \leq state.onHand

=============================================================================
