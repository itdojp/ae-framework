# Operate: Runtime Conformance Monitor (Draft)

## Purpose

`ae operate:monitor` consumes runtime traces and maps them to spec variables/actions.
It validates partial traces through the verifier adapter and emits violation summaries
for CI or long‑running monitoring.

## Inputs

- **Spec**: TLA+/formal spec directory (e.g., `spec/`).
- **Trace source**: log files, NDJSON events, or a stream endpoint.
- **Trace map**: `trace-map.yaml` describing how events map to spec fields.

## Trace map format

The trace map is a YAML/JSON document validated by `schema/trace-map.schema.json`.
It defines:

- **time**: how to read event timestamps.
- **correlationKeys**: how to group events (trace/span/session).
- **mappings**: event match rules + variable assignments + optional action name.

### Example

See `fixtures/trace-map/sample.trace-map.json` for a minimal example.

```yaml
schemaVersion: 0.1.0
spec:
  module: OrderSpec
  variables: [orders]
  actions: [PlaceOrder]
time:
  field: timestamp
  format: iso8601
correlationKeys:
  - name: traceId
    field: traceId
    required: true
mappings:
  - name: order.placed
    match:
      field: event
      equals: order.placed
    action: PlaceOrder
    assigns:
      - variable: orders
        value: $.payload.orderId
```

## CLI (planned)

```bash
ae operate:monitor --spec spec/ --source logs/ --map trace-map.yaml --mode ci
```

## Status

This document defines the initial contract only. Implementation and CI wiring
are tracked in issue #1070.
