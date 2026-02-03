------------------------- MODULE KvOnceImpl -------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS Keys, Values, NULL, MAX_RETRIES, MAX_EVENTS
VARIABLES store, retries, events

ASSUME NULL \notin Values
ASSUME MAX_RETRIES \in Nat
ASSUME MAX_EVENTS \in Nat

Init ==
  /\ store = [k \in Keys |-> [written |-> FALSE, val |-> NULL]]
  /\ retries = [k \in Keys |-> 0]
  /\ events = << >>

CanAppend ==
  Len(events) < MAX_EVENTS

Put(k, v) ==
  /\ k \in Keys
  /\ v \in Values
  /\ ~store[k].written
  /\ CanAppend
  /\ store' = [store EXCEPT ![k] = [written |-> TRUE, val |-> v]]
  /\ retries' = retries
  /\ events' = Append(events, [
        type |-> "success",
        key |-> k,
        value |-> v,
        reason |-> NULL
      ])

Retry(k, reason) ==
  /\ k \in Keys
  /\ retries[k] < MAX_RETRIES
  /\ CanAppend
  /\ store' = store
  /\ retries' = [retries EXCEPT ![k] = retries[k] + 1]
  /\ events' = Append(events, [
        type |-> "retry",
        key |-> k,
        value |-> NULL,
        reason |-> reason
      ])

Failure(k, reason) ==
  /\ k \in Keys
  /\ CanAppend
  /\ store' = store
  /\ retries' = retries
  /\ events' = Append(events, [
        type |-> "failure",
        key |-> k,
        value |-> NULL,
        reason |-> reason
      ])

Next ==
  \E k1 \in Keys, v \in Values: Put(k1, v)
  \/ \E k2 \in Keys: Retry(k2, "transient")
  \/ \E k3 \in Keys: store[k3].written /\ Failure(k3, "duplicate")

TypeInvariant ==
  /\ store \in [Keys -> [written: BOOLEAN, val: Values \cup {NULL}]]
  /\ retries \in [Keys -> Nat]
  /\ events \in Seq([
        type: {"success", "retry", "failure"},
        key: Keys,
        value: Values \cup {NULL},
        reason: STRING \cup {NULL}
      ])
  /\ Len(events) <= MAX_EVENTS

NoOverwrite == \A k \in Keys: store[k].written => store[k].val # NULL

RetryBounded == \A k \in Keys: retries[k] <= MAX_RETRIES

Spec == Init /\ [][Next]_{<<store, retries, events>>}

Invariant == TypeInvariant /\ NoOverwrite /\ RetryBounded

THEOREM KvOnceImplSafety == Spec => []Invariant
===================================================================
