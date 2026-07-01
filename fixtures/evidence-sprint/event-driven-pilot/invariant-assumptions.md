# Event-driven Pilot Invariant Assumptions: Evidence Sprint event replay

This fixture records the ordering and invariant assumptions for Issue #3573. It
is deterministic and report-only; it does not add a runtime event processor,
message broker, or production workflow implementation.

## Selected small event-driven change

Use the existing inventory trace sample as a replayable event fixture for an
internal assurance review surface:

```text
InventoryAllocated -> InventoryUpdated
```

Source trace fixture: `samples/conformance/sample-traces.json`.

## Ordering assumptions

| Assumption | Rule |
| --- | --- |
| Trace grouping | Events with the same `traceId` belong to one replay sequence. |
| Timestamp order | Events in a replay sequence must be processed in non-decreasing timestamp order. |
| Causal order | `InventoryUpdated` must not be reviewed before the preceding `InventoryAllocated` event in this sample sequence. |
| Actor consistency | Events in this fixture are emitted by `inventory-service`; a future multi-actor sample must state handoff semantics explicitly. |
| Replay determinism | Replay validation must not call live external APIs, clocks, queues, or brokers. |

## Invariant assumptions

| Invariant | Review meaning |
| --- | --- |
| Non-negative inventory | `state.onHand` and `state.allocated` are non-negative after every event. |
| Allocation bounded by stock | `state.allocated <= state.onHand` after every event. |
| Successful outcome retained | Each sample event has `outcome = success`; failure events require separate compensating-event assumptions. |
| Append-only trace | The replay sequence is inspected as append-only evidence; the pilot does not mutate the source trace. |
| Selected-trace conformance | The selected conformance evidence is `node scripts/formal/verify-conformance.mjs --in samples/conformance/sample-traces.json`, so generic `configs/samples` rule findings are not used as evidence for this pilot trace. |

## Escalation rule

Escalate to human maintainer review and property/model/formal lanes if replay is
non-deterministic, an invariant fails, ordering assumptions are disputed, or a
future domain sample is payment/auth/safety critical.
