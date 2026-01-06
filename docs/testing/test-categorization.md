# Test Categorization Strategy

> 🌍 Language / 言語: English | 日本語

## Overview

This document summarizes how tests are grouped in ae-framework so contributors can select the right suite for local runs, CI, and investigation.

## Categories

| Category | Primary purpose | Typical scripts | Notes |
| --- | --- | --- | --- |
| **Fast / Unit** | Quick feedback on core logic | `pnpm run test:fast`, `pnpm run test:unit` | Use for local iteration and pre-commit checks. |
| **Integration** | Validate cross-module behavior | `pnpm run test:int`, `pnpm run test:integration:webapi` | Higher cost; usually run in CI or before release. |
| **Property-based** | Explore edge cases via generators | `pnpm run test:property`, `pnpm run pbt` | Prefer for invariants and fuzz-friendly logic. |
| **Model-based (MBT)** | Stateful behavior verification | `pnpm run test:mbt`, `pnpm run test:mbt:ci` | Uses model traces; keep deterministic inputs. |
| **Mutation** | Detect weak tests | `pnpm run mutation`, `pnpm run pipelines:mutation:quick` | Run selectively or in scheduled CI. |
| **Formal / Model Check** | Spec-level guarantees | `pnpm run verify:formal`, `pnpm run verify:tla`, `pnpm run verify:alloy` | Requires formal specs and external tools. |
| **Quality Gates** | Policy/threshold enforcement | `pnpm run quality:gates`, `pnpm run quality:gates:dev` | Centralized quality policy (lint/coverage/security/etc). |
| **Security** | Dependency and SBOM checks | `pnpm run security:integrated:quick`, `pnpm run security:integrated:full` | Use quick mode for PRs, full for scheduled runs. |
| **Extended CI** | Full integration pipeline | `pnpm run test:ci:lite`, `pnpm run test:ci:extended` | Used by CI workflows for gating. |

## Guidance

- **Local dev**: start with `test:fast` and narrow to the suite you are editing.
- **Before PR**: `test:ci:lite` (verify-lite) for a balanced signal.
- **Nightly / heavy**: run mutation, MBT, and full formal checks for regression coverage.

## Related

- Parallel execution strategy: `docs/testing/parallel-execution-strategy.md`
