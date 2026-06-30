---
docRole: ssot
canonicalSource:
- docs/architecture/CURRENT-SYSTEM-OVERVIEW.md
- docs/architecture/ZERO-BASED-IDEAL-DESIGN.md
- docs/reference/CONTRACT-CATALOG.md
- policy/risk-policy.yml
lastVerified: '2026-07-01'
owner: quality-maintainers
verificationCommand: pnpm -s run check:doc-consistency
---

# Code Quality Baseline

This document defines the report-only code quality baseline introduced for Re-evaluation 3. It records the current quality control surfaces, architecture ownership boundaries, known exceptions, and the promotion rule for any future blocking gate. It does not add a new merge-blocking condition for ordinary pull requests.

## Purpose

The baseline makes the following surfaces explicit:

- type safety status and the command used to observe it;
- lint debt and local lint execution status;
- dependency boundary and cyclic-import checks;
- duplicated or sprawling execution surfaces such as package scripts and workflows;
- public entrypoints that must not be removed accidentally;
- intentional exceptions tracked as data with owner, reason, review date, and cleanup surface.

## Artifact contract

| Item | Value |
| --- | --- |
| JSON artifact | `artifacts/quality/code-quality-baseline.json` |
| Markdown artifact | `artifacts/quality/code-quality-baseline.md` |
| Schema | `schema/quality-baseline.schema.json` |
| Generator | `scripts/quality/collect-code-quality-baseline.mjs` |
| Package script | `pnpm run quality:baseline` |
| Enforcement mode | report-only |

The generator defaults `generatedAt` to `1970-01-01T00:00:00.000Z` so repeated local runs are deterministic. Operators can pass an explicit timestamp when a live evidence timestamp is required:

```bash
pnpm run quality:baseline -- --generated-at 2026-07-01T00:00:00.000Z
```

The command writes both JSON and Markdown under `artifacts/quality/`. These files are runtime evidence and are not required to be committed for ordinary pull requests.

## Baseline commands

The baseline records whether the following commands are configured. With `--run-checks`, the generator executes them and records `pass` or `fail`; without it, the artifact records deterministic `configured` / `missing` status.

| Surface | Command | Role |
| --- | --- | --- |
| Type safety | `pnpm run types:check` | Verifies the repository TypeScript verification project. |
| Lint debt | `pnpm run lint` | Tracks ESLint health and style regressions. |
| Fast regression tests | `pnpm run test:fast` | Represents the ordinary PR regression baseline. |
| Documentation consistency | `pnpm -s run check:doc-consistency` | Keeps documented commands, paths, and contract references aligned. |
| Dependency cycles | `pnpm run lint:deps` | Uses the import graph to keep cyclic dependencies visible. |
| Context Pack dependencies | `pnpm run context-pack:deps` | Keeps design-boundary dependency drift report-only and observable. |

## Architecture plane ownership

| Plane | Owned surfaces | Guardrail |
| --- | --- | --- |
| Control | Context Pack, boundary map, Contract Catalog | Design SSOT and artifact-contract changes must be validated before implementation slices rely on them. |
| Policy | `policy/risk-policy.yml`, `policy-gate`, CI policy docs | Risk and enforcement decisions stay policy-owned and report-only signals are promoted only by explicit policy change. |
| Execution | `package.json`, `scripts/ci/`, `scripts/quality/`, workflows | Local and CI execution should share named package scripts where practical; compatibility routes require ledger entries. |
| Evidence | `schema/`, `fixtures/`, `artifacts/quality/` | Machine-readable artifacts need schema coverage, fixtures, and catalog registration. |
| Observability | metrics scripts, reports, operating docs | Trends and stop rules should reference observable evidence rather than reviewer memory. |

## Debt ledger

Intentional exceptions are stored in `docs/quality/code-quality-debt-ledger.json`. Each entry must include:

- `id`: stable exception identifier;
- `owner`: role accountable for review and cleanup;
- `reason`: why the exception exists;
- `reviewAfter`: date for reassessment;
- `targetCleanupSurface`: files, commands, or routes expected to change when the exception is removed;
- `source`: primary documentation or code surface explaining the exception;
- `links`: supporting file references.

Known exceptions must be represented in this ledger rather than hidden in source comments or release notes. The quality baseline generator reads the ledger and surfaces the exception count and top cleanup candidates.

## Report-only CI policy

Issue #3547 intentionally introduces visibility, not enforcement. The baseline may be generated locally or in a future report-only workflow, but ordinary PRs remain governed by the existing required checks (`verify-lite` and `policy-gate`).

A baseline metric can become blocking only after a later issue and pull request document all of the following:

1. deterministic generation across local and CI environments;
2. schema and fixture coverage;
3. stable false-positive handling and exception ownership;
4. branch-protection impact and rollback plan;
5. explicit policy-gate or workflow change showing the new enforcement path.

## Japanese summary / 日本語要約

このベースラインは、型検査、lint、依存境界、公開エントリポイント、script/workflow の増加、既知の例外を機械可読に可視化するための report-only 成果物です。通常PRの必須ゲートは追加しません。将来 blocking 条件へ昇格する場合は、決定性、スキーマ/fixture、例外台帳、branch protection 影響、ロールバック方針を別Issue/PRで明示します。
