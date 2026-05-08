---
docRole: ssot
lastVerified: '2026-05-08'
owner: testing-docs
verificationCommand: pnpm -s run check:doc-consistency
---
# Test Categorization Strategy

> 🌍 Language / 言語: English | 日本語

## Overview

This document summarizes how tests are grouped in ae-framework so contributors can select the right suite for local runs, CI, and investigation. For the route-by-context index, coverage baseline treatment, and label map, start with `docs/testing/README.md`.

## Categories

| Category | Primary purpose | Typical scripts | Cost | CI label / control | Notes |
| -------- | --------------- | -------------- | ---- | ------------------ | ----- |
| **Fast / Unit** | Quick feedback on core logic | `pnpm run test:fast`, `pnpm run test:unit` | S | default `verify-lite` path | Use for local iteration and pre-commit checks. |
| **Contract** | Validate schema, artifact, and output compatibility | `pnpm run test:contracts` | S-M | `enforce-artifacts` when artifact validation should block | Pair with schema and fixture updates. |
| **Integration** | Validate cross-module behavior | `pnpm run test:int`, `pnpm run test:integration:webapi` | M-L | `run-ci-extended`, `run-integration` | Higher cost; usually run in CI or before release. |
| **Property-based** | Explore edge cases via generators | `pnpm run test:property`, `pnpm run pbt` | M-L | `run-property`, optional `enforce-testing` | Prefer for invariants and fuzz-friendly logic. |
| **Model-based (MBT)** | Stateful behavior verification | `pnpm run test:mbt`, `pnpm run test:mbt:ci` | L-XL | `run-mbt` | Uses model traces; keep deterministic inputs. |
| **Mutation** | Detect weak tests | `pnpm run mutation`, `pnpm run pipelines:mutation:quick` | XL | `run-mutation` | Run selectively or in scheduled CI. |
| **Formal / Model Check** | Spec-level guarantees | `pnpm run verify:formal`, `pnpm run verify:tla`, `pnpm run verify:alloy` | XL | scheduled/manual, plus risk labels when needed | Requires formal specs and external tools. |
| **Quality Gates** | Policy/threshold enforcement | `pnpm run quality:gates`, `pnpm run quality:gates:dev` | M | policy labels such as `risk:high` | Centralized quality policy for lint, coverage, security, and evidence gates. |
| **Security** | Dependency, SBOM, and security-assurance evidence | `pnpm run test:security-assurance`, `pnpm run security:integrated:quick`, `pnpm run security:integrated:full` | M-XL | `run-security` | Use quick mode for PRs, full mode or fixtures for scheduled assurance refreshes. |
| **Coverage** | Coverage summary and coverage-gate evidence | `pnpm run coverage` | M-L | `enforce-coverage`, `coverage:<pct>` | `coverage/` output is generated evidence, not a manually maintained tracked baseline. |
| **Extended CI** | Full integration pipeline | `pnpm run test:ci:lite`, `pnpm run test:ci:extended` | M-L | `run-ci-extended` and narrower heavy-lane labels | Used by CI workflows for gating and opt-in assurance. |

## Guidance

- **Local dev**: start with `test:fast` and narrow to the suite you are editing.
- **Before PR**: use `verify:lite` or `test:ci:lite` for the default required-check signal.
- **Contract-sensitive changes**: add `test:contracts` and focused schema or artifact fixture checks.
- **High-risk / nightly / heavy**: run property, MBT, mutation, and formal checks based on the risk surface and labels documented in `docs/testing/README.md`.
- **Coverage-sensitive changes**: run `pnpm run coverage` and treat `coverage/` as generated evidence. Record the commit, command, and environment when quoting a baseline.

## CI gating notes

- Heavy suites are **label-gated** to avoid unstable or expensive runs on every PR.
- Use `docs/ci/label-gating.md` for labels (`run-ci-extended`, `run-mbt`, `run-mutation`, `run-property`, `enforce-coverage`).
- Prefer the stable profile for CI baselines: `docs/ci/stable-profile.md`.

## Related

- `docs/testing/README.md`
- `docs/testing/parallel-execution-strategy.md`
- `docs/quality/coverage-policy.md`
