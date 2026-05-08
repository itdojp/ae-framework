---
docRole: narrative
canonicalSource:
  - fixtures/assurance-e2e/inventory-waiver/README.md
  - docs/reports/ASSURANCE-CONTROL-PLANE-E2E-VALIDATION.md
lastVerified: '2026-05-08'
---

# Assurance Control Plane E2E Example

This example shows the smallest checked-in fixture for the assurance-control-plane path:

```text
requirement refs
  -> claims
  -> evidence manifest
  -> claim-level achieved summary
  -> policy decision
  -> proof-carrying change package summary
```

Run it with:

```bash
pnpm -s run assurance:e2e -- --scenario inventory-waiver
```

Expected output includes:

- `claim evidence claims: 3`
- `claim-level claims: 3`
- `waived claims: 1`
- `policy assurance result: waived`
- `change-package assurance status: partial`
- `comparison: ok`

Fixture and report:

- Fixture README: `fixtures/assurance-e2e/inventory-waiver/README.md`
- Validation report: `docs/reports/ASSURANCE-CONTROL-PLANE-E2E-VALIDATION.md`
- Golden artifacts: `fixtures/assurance-e2e/inventory-waiver/expected/`

The example intentionally includes non-green assurance states. `manual-fraud-review` is waived, `no-negative-balance` remains below its target assurance level, and `no-negative-stock` is runtime-mitigated rather than proof-backed.
