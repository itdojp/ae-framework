# SPECA-like security import fixture

This fixture is intentionally SPECA-compatible rather than SPECA-complete. It models the minimum inputs used by `ae security import-speca`:

- `01e_security_properties.json`: extracted security properties / claims
- `02c_threats.json`: STRIDE and CWE tags linked to properties
- `03_audit_findings.json`: proof-attempt audit gaps / candidate findings
- `04_review_gates.json`: Dead Code / Trust Boundary / Scope review gate results

Unsupported fields such as `specaPhaseNote`, `likelihood`, `rawGapScore`, and `confidenceScore` are retained as import warnings in `import-summary.json` and `import-summary.md` instead of being silently discarded.
