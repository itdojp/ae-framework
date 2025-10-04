------------------------- MODULE KvOnceImpl -------------------------
EXTENDS Naturals, Sequences

CONSTANTS Keys, Values, NULL, MAX_RETRIES
VARIABLES store, retries, events

ASSUME NULL \notin Values
ASSUME MAX_RETRIES \in Nat

Init ==
  /\ store = [k \in Keys |-> [written |-> FALSE, val |-> NULL]]
  /\ retries = [k \in Keys |-> 0]
  /\ events = << >>

Put(k, v) ==
  /\ k \in Keys
  /\ v \in Values
  /\ ~store[k].written
  /\ store' = [store EXCEPT ![k] = [written |-> TRUE, val |-> v]]
  /\ retries' = retries
  /\ events' = Append(events, [type |-> "success", key |-> k, value |-> v])

Retry(k, reason) ==
  /\ k \in Keys
  /\ retries[k] < MAX_RETRIES
  /\ store' = store
  /\ retries' = [retries EXCEPT ![k] = retries[k] + 1]
  /\ events' = Append(events, [type |-> "retry", key |-> k, reason |-> reason])

Failure(k, reason) ==
  /\ k \in Keys
  /\ store' = store
  /\ retries' = retries
  /\ events' = Append(events, [type |-> "failure", key |-> k, reason |-> reason])

Next ==
  \E k \in Keys, v \in Values: Put(k, v)
  \/ \E k \in Keys: Retry(k, "transient")
  \/ \E k \in Keys: store[k].written /\ Failure(k, "duplicate")

TypeInvariant ==
  /\ store \in [Keys -> [written: BOOLEAN, val: Values \cup {NULL}]]
  /\ retries \in [Keys -> Nat]
  /\ events \in Seq(
        [type: "success", key: Keys, value: Values]
        \cup [type: "retry", key: Keys, reason: STRING]
        \cup [type: "failure", key: Keys, reason: STRING]
     )

NoOverwrite == \A k \in Keys: store[k].written => store[k].val # NULL

RetryBounded == \A k \in Keys: retries[k] <= MAX_RETRIES

Spec == Init /\ [][Next]_{<<store, retries, events>>}

Invariant == TypeInvariant /\ NoOverwrite /\ RetryBounded

THEOREM KvOnceImplSafety == Spec => []Invariant
===================================================================
