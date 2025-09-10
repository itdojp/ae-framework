----------------------------- MODULE Inventory -----------------------------
EXTENDS Naturals, Sequences
CONSTANTS MaxStock
VARIABLES stock, reserved

\* Scenario: successful-reservation @inventory @reservation
\* Scenario: prevent-negative-stock @inventory @safety
\* Scenario: idempotent-by-order-id @inventory @idempotency

Init == /\ stock = MaxStock /\ reserved = [o \in {} |-> 0]

Reserve(o, q) ==
  /\ q \in Nat
  /\ q > 0
  /\ reserved' = [reserved EXCEPT ![o] = reserved[o] + q]
  /\ stock' = stock - q

DoubleBookingFree == \A o \in DOMAIN reserved: reserved[o] <= stock + reserved[o]
NonNegative == stock >= 0

Next == \E o, q: Reserve(o, q)

Inv == NonNegative

vars == << stock, reserved >>
Spec == Init /\ [][Next]_vars

============================================================================
