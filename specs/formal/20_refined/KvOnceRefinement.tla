--------------------- MODULE KvOnceRefinement ---------------------
EXTENDS Naturals, Sequences

CONSTANTS Keys, Values, NULL, MAX_RETRIES
VARIABLES store, retries

ASSUME NULL \notin Values
ASSUME MAX_RETRIES \in Nat

Init ==
  /\ store = [k \in Keys |-> [written |-> FALSE, val |-> NULL]]
  /\ retries = [k \in Keys |-> 0]

Put(k, v) ==
  /\ k \in Keys
  /\ v \in Values
  /\ retries[k] < MAX_RETRIES
  /\ ~store[k].written
  /\ store' = [store EXCEPT ![k] = [written |-> TRUE, val |-> v]]
  /\ retries' = [retries EXCEPT ![k] = retries[k] + 1]

Retry(k) ==
  /\ k \in Keys
  /\ retries[k] < MAX_RETRIES
  /\ store' = store
  /\ retries' = [retries EXCEPT ![k] = retries[k] + 1]

Next ==
  \E k \in Keys, v \in Values: Put(k, v)
  \/ \E k \in Keys: Retry(k)

TypeInvariant ==
  /\ store \in [Keys -> [written: BOOLEAN, val: Values \cup {NULL}]]
  /\ retries \in [Keys -> Nat]
  /\ \A k \in Keys: retries[k] <= MAX_RETRIES

NoOverwrite == \A k \in Keys: store[k].written => store[k].val # NULL

Spec == Init /\ [][Next]_{<<store, retries>>}

Invariant == TypeInvariant /\ NoOverwrite

THEOREM KvOnceRefinementSafety == Spec => []Invariant
=================================================================
