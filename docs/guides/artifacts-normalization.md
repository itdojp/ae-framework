# Artifacts Normalization Policy

- Store machine-readable results as JSON and JUnit only.
- Paths:
  - `artifacts/*/summary.json` for adapters
  - `formal/summary.json` for formal verification
  - `artifacts/properties/summary.json` for property tests
- Conform to schemas in `docs/schemas/`.
- Include `traceId` wherever applicable.
