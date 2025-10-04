--------------------------- MODULE KvOnce ---------------------------
EXTENDS Naturals

CONSTANTS Keys, Values, NULL
VARIABLES store

ASSUME NULL \notin Values

TypeInvariant == store \in [Keys -> [written: BOOLEAN, val: Values \cup {NULL}]]

Init == store = [k \in Keys |-> [written |-> FALSE, val |-> NULL]]

Put(k, v) ==
  /\ k \in Keys
  /\ v \in Values
  /\ ~store[k].written
  /\ store' = [store EXCEPT ![k] = [written |-> TRUE, val |-> v]]

Next == \E k \in Keys, v \in Values: Put(k, v)

NoOverwrite == \A k \in Keys: store[k].written => store[k].val # NULL

Spec == Init /\ [][Next]_store

Invariant == TypeInvariant /\ NoOverwrite

THEOREM KvOnceSafety == Spec => []Invariant
====================================================================
