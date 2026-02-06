------------------------------ MODULE DomainSpec ------------------------------
EXTENDS Naturals, Sequences

(* Minimal skeleton for illustration. Replace with domain-specific spec. *)

CONSTANTS
  \* @type: Int;
  MaxQty,
  \* @type: Int;
  MaxOnHand

VARIABLES
  \* @type: { onHand: Int, allocated: Int };
  state

ASSUME MaxQty \in Nat /\ MaxOnHand \in Nat /\ MaxQty > 0 /\ MaxOnHand > 0

Qty == 1..MaxQty

Init == state = [ onHand |-> 0, allocated |-> 0 ]

Next == 
  \/ \E qty \in Qty : state.onHand + qty <= MaxOnHand /\ state' = [state EXCEPT !.onHand = @ + qty]
  \/ \E qty \in Qty : state.allocated + qty <= state.onHand /\ state' = [state EXCEPT !.allocated = @ + qty]
  \/ \E qty \in Qty : qty <= state.allocated /\ state' = [state EXCEPT !.allocated = @ - qty, !.onHand = @ - qty]

Spec == Init /\ [][Next]_state

Invariant == state.onHand \geq 0 /\ state.allocated \leq state.onHand /\ state.onHand <= MaxOnHand

=============================================================================
