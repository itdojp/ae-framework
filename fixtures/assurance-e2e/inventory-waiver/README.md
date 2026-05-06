# Inventory Waiver Assurance E2E Scenario

This fixture freezes a lightweight end-to-end assurance scenario for an
inventory reservation change. It is intentionally fixture-backed: the goal is
to verify the contract and renderer path without making formal full-run or
heavy CI lanes mandatory.

## Scenario

The scenario contains three claims:

| Claim | Expected state | Purpose |
| --- | --- | --- |
| `no-negative-stock` | `satisfied` | Fully supported claim imported from `assurance-summary/v1`. |
| `no-negative-balance` | `partial` | Partially supported claim imported from `change-package/v2` with missing evidence retained. |
| `manual-fraud-review` | `waived` | Waiver-backed claim that remains distinct from `pass`. |

The golden output fixes the path from:

1. `verify-lite-run-summary`
2. `assurance-summary`
3. `claim-evidence-manifest`
4. `policy-input`
5. `policy-decision`
6. `policy-gate-summary`

## Layout

- `inputs/` contains deterministic source artifacts for the scenario.
- `expected/` contains golden artifacts generated from those inputs.

Actual run output is written outside this fixture directory by default under
`artifacts/assurance-e2e/<scenario>/<generated-at>/`.

## Run

```bash
pnpm -s run assurance:e2e -- --scenario inventory-waiver
```

For a deterministic local output directory:

```bash
pnpm -s run assurance:e2e -- \
  --scenario inventory-waiver \
  --output-dir artifacts/assurance-e2e/inventory-waiver/latest
```

## Updating golden artifacts

Only update expected artifacts after reviewing the generated diff and confirming
that the contract or renderer change is intentional.

```bash
pnpm -s run assurance:e2e -- \
  --scenario inventory-waiver \
  --output-dir artifacts/assurance-e2e/inventory-waiver/latest \
  --update-expected
```

## Reading the artifacts

- `expected/verify-lite-run-summary.json` confirms the lightweight verification
  lane is green for the scenario.
- `expected/assurance-summary.json` provides the fully supported claim anchor.
- `expected/claim-evidence-manifest.json` is the claim-level evidence manifest.
  It should show `fullySupported=1`, `partiallySupported=1`, and `waived=1`.
- `expected/policy-decision-js-v1.json` verifies that policy-gate reports
  `assurance.result=waived` in report-only mode rather than treating the waiver
  as a pass.
- `expected/policy-gate-summary.md` is the human-readable reviewer summary.

## Regression triage

If the runner reports drift:

1. Inspect the changed files under the actual output directory.
2. Determine whether the difference is an intentional contract / renderer
   change or an unintended regression.
3. If intentional, rerun with `--update-expected` and include the changed
   golden artifacts in the PR.
4. If unintended, fix the generator, evaluator, or renderer before updating
   expected artifacts.
