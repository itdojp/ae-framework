# Release Engineering (Policy v1)

This document defines the initial release-policy contract introduced for Issue #2288.

## Goal

- Separate deployment execution from release decision.
- Make rollout and rollback criteria machine-readable.
- Reuse the same policy in CLI/CI operations.

## Source of truth

- Policy file: `policy/release-policy.yml`
- Schema: `schema/release-policy.schema.json`
- JSON fixture for schema validation: `fixtures/release/sample.release-policy.json`

## Policy structure (`ae-release-policy/v1`)

- `rolloutStrategy`
  - `mode`: `canary | progressive | blue-green`
  - `percentSteps`: rollout sequence
  - `pauseSeconds`: wait time between steps
  - `maxDurationSeconds`: upper bound for full rollout
- `healthSignals`
  - Named signal definitions (for example `errorRate`, `p95LatencyMs`, `saturation`)
  - Each signal declares `metricKey`, warning/critical thresholds, and comparison mode (`lte`/`gte`)
- `rollbackPolicy`
  - Enable/disable switch
  - Trigger mode (`any-critical | all-critical | manual`)
  - Hook settings (`type`, optional `command`, `timeoutSeconds`)
- `requiredEvidence`
  - Global required evidence list for release decisions
- `environments`
  - Environment-specific rollout steps and required evidence

## Governance

- Changes to `policy/release-policy.yml` are treated as high risk by `policy/risk-policy.yml`.
- Schema validation is enforced by `scripts/ci/validate-json.mjs`.
