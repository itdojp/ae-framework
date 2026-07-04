# Deploy-time profile dogfood fixtures

`recent-pr-gate-decisions.json` is a deterministic fixture-equivalent replay set for Issue #3619.
It avoids live GitHub history in CI while preserving the decision surface that matters for
profile dogfooding: the required deploy-time profile checks `verify-lite`, `policy-gate`, and
`gate`.

The set intentionally contains 20 PR-equivalent cases, including successful merges and two
blocking outcomes. Optional standard/full lanes are represented as advisory check conclusions;
they are recorded in the report but do not change the current required-check decision.
