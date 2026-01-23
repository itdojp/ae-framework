# Formal Plan Schema (formal.yaml)

This document defines the `formal.yaml` contract exchanged between the **Planning** and **Coding** stages of `ae formal:auto`.
The YAML format is equivalent to the JSON schema at `schema/formal-plan.schema.json`.

## Purpose

`formal.yaml` captures the planner's structured understanding of the problem:
- state variables and constants
- action definitions (Init/Next candidates)
- invariants and liveness goals
- assumptions and requirements

The coder uses this contract to emit a TLA+ module skeleton.

## Schema

- **Schema file**: `schema/formal-plan.schema.json`
- **Fixture**: `fixtures/formal-plan/sample.formal-plan.json`

### Required fields

| Field | Type | Description |
| --- | --- | --- |
| `schemaVersion` | string | Semantic version for the schema (e.g., `0.1.0`). |
| `metadata` | object | Source and timestamp information. |
| `variables` | array | State variables with their types. |
| `actions` | array | Action candidates with TLA+ fragments. |
| `invariants` | array | Safety properties to enforce. |

### Optional fields

| Field | Type | Description |
| --- | --- | --- |
| `requirements` | array | Natural-language requirements the planner extracted. |
| `constants` | array | Constants and domain annotations. |
| `liveness` | array | Liveness properties (`<>`, `[]<>`). |
| `assumptions` | array | Environmental assumptions and constraints. |

## Example

```json
{
  "schemaVersion": "0.1.0",
  "metadata": {
    "source": "formalize-planner",
    "generatedAt": "2026-01-01T00:00:00Z"
  },
  "variables": [
    {"name": "tokens", "type": "Int"},
    {"name": "capacity", "type": "Int"}
  ],
  "actions": [
    {"name": "Init", "tla": "tokens = 0 /\\ capacity \\in Nat"},
    {"name": "Refill", "tla": "tokens' = Min(capacity, tokens + 1)"}
  ],
  "invariants": [
    {"name": "CapInvariant", "tla": "tokens <= capacity"}
  ]
}
```

## Validation

The fixture is validated in CI via `scripts/ci/validate-json.mjs`.
If you edit the schema, update the fixture accordingly.
