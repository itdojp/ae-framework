# Observability

- Trace schema: `trace-schema.yaml` defines minimal fields for conformance.
- Emit traces conforming to this schema when integrating runtime checks.

Example event (YAML):

```
traceId: "sess-2025-09-12T10:00:03Z-001"
timestamp: "2025-09-12T10:00:03Z"
actor: "checkout-service"
event: "OrderPlaced"
action: "CreateOrder"
state:
  items: 3
  total: 4200
outcome: success
```

