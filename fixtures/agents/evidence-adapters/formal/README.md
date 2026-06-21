# Formal / model checker fixture

Raw fixture: `model-check-output.json`

## Producer boundary

Formal tool output supports only the modeled/proved scope, assumptions, and counterexample state captured in the artifact. It is not product-wide proof.

## Expected normalized routing

- `formal-summary/v2` for model/proof scope, assumptions, and counterexample state.
- `producer-normalization-summary/v1` for report-only routing of raw formal-tool signals.
- `claim-evidence-manifest/v1` for scoped formal evidence and partial out-of-scope claims.
- `assurance-summary/v1` for reviewer-first lane evidence and residual assumptions.
- Optional `change-package/v2` when formal model files change.

Out-of-scope production behavior remains partial or unresolved until separate evidence exists.
