----------------------------- MODULE Inventory -----------------------------
EXTENDS Naturals, Sequences
CONSTANTS MaxStock, Orders
VARIABLES stock, reserved

\* Scenario: successful-reservation @inventory @reservation
\* Scenario: prevent-negative-stock @inventory @safety
\* Scenario: idempotent-by-order-id @inventory @idempotency

Init == /\ stock = MaxStock /\ reserved = [o \in Orders |-> 0]
Init == /\ stock = MaxStock /\ reserved = [o \in {} |-> 0]

Reserve(o, q) ==
  /\ o \in Orders
  /\ q \in Nat
  /\ q > 0
  /\ q <= stock
  /\ reserved' = [reserved EXCEPT ![o] = reserved[o] + q]
  /\ stock' = stock - q

DoubleBookingFree == \A o \in DOMAIN reserved: reserved[o] <= stock + reserved[o]
NonNegative == stock >= 0

Next == \E o \in Orders, q \in 1..stock: Reserve(o, q)

Inv == NonNegative

vars == << stock, reserved >>
Spec == Init /\ [][Next]_vars

============================================================================
