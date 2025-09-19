# Quality Threshold Precedence and Migration

Precedence
- policy > AE-IR > ae.config
  - policy: Single Source of Truth (SSOT). See `policy/quality.json`.
  - AE-IR: Derived artifacts/specs may provide contextual inputs, but do not override policy.
  - ae.config: Developer-local hints only; do not affect enforcement.

CLI Behavior
- When `ae.config.ts` contains `qa.coverageThreshold`, the QA CLI warns once per run:
  - ae.config thresholds are hints; policy is the source of truth
  - Precedence is displayed: `policy > AE-IR > ae.config`
  - Migration guidance points to `policy/quality.json`
- Suppress hint warnings via environment variable:
  - `AE_SUPPRESS_CONFIG_HINTS=true`

Migration Example (ae.config → policy)
- Current ae.config hint:
  ```ts
  // ae.config.ts
  export default {
    qa: { coverageThreshold: { lines: 90, functions: 90, branches: 85, statements: 90 } }
  }
  ```
- Move to policy thresholds (enforced):
  ```json
  // policy/quality.json (under quality.coverage.thresholds)
  {
    "quality": {
      "coverage": {
        "thresholds": {
          "lines": 90,
          "functions": 90,
          "branches": 85,
          "statements": 90
        }
      }
    }
  }
  ```
- Optional: choose profile via `AE_QUALITY_PROFILE` (default in CI is `ci`).

Notes
- CI decision logic and policy loader semantics are unchanged by this migration.
- Keep ae.config hints for local visibility if useful; warnings can be suppressed in CI logs.
