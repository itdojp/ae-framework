---
docRole: narrative
lastVerified: '2026-03-12'
owner: repo-maintenance
verificationCommand: pnpm run maintenance:artifact:inventory
---
# Artifact Reference Layout Plan

## Summary
`artifacts/` の tracked ファイルは、現状でも `repo-layout-policy` 上は 4 類型に分類できるが、reference snapshot が `artifacts/reference/` と補助サブディレクトリの双方に分散している。

この文書は `Issue #2585` の planning memo として、tracked artifact inventory と小粒 PR の投入順を定義する。

## Current Inventory
`pnpm run maintenance:artifact:inventory` の最新出力では、tracked artifact は以下に分類される。

- committed contract artifact: `artifacts/types/**`, `artifacts/contracts/**`, `artifacts/domain/**`, `artifacts/plan/**`, `artifacts/api/**`, `artifacts/bdd/**`, `artifacts/properties/**`, `artifacts/repros/**`, `artifacts/public-types.current.d.ts`
- reference snapshot: `artifacts/reference/benchmarks/*`, `artifacts/reference/verify/*`, `artifacts/reference/types/*` に加え、`artifacts/hermetic-reports/**`, `artifacts/validation-results/**`
- archive: `artifacts/archive/**`
- local debug archive: `artifacts/codex/**`

## Proposed Normalization
### Keep in place
- `artifacts/types/**`, `artifacts/contracts/**`, `artifacts/domain/**`, `artifacts/plan/**`, `artifacts/api/**`, `artifacts/bdd/**`, `artifacts/properties/**`, `artifacts/repros/**`
- `artifacts/public-types.current.d.ts`
- `artifacts/archive/**`
- `artifacts/codex/**`（ignored-by-default の local debug archive）

### Keep under `artifacts/reference/**`
- benchmark baseline
  - `artifacts/reference/benchmarks/bench.json`
  - `artifacts/reference/benchmarks/bench.md`
  - `artifacts/reference/benchmarks/bench-1.json`
  - `artifacts/reference/benchmarks/bench-2.json`
  - status: normalized in `PR #2629`
- verification snapshots
  - `artifacts/reference/verify/verify.md`
  - `artifacts/reference/verify/recovery-verify.md`
  - `artifacts/reference/verify/verify-lite-lint-summary.json`
  - status: normalized in `PR #2632` (tracked by `Issue #2631`)
- type/reference validation snapshots
  - `artifacts/reference/types/types-gate-ci-validation.md`
  - `artifacts/reference/types/types-hardening-validation.md`
  - status: normalization tracked under `Issue #2633`

### Move to `artifacts/reference/**`
- hermetic/validation snapshots
  - `artifacts/hermetic-reports/**`
  - `artifacts/validation-results/**`
  - target: `artifacts/reference/hermetic-reports/**`, `artifacts/reference/validation-results/**`

## Consumer Impact
現時点の root-level tracked snapshot の consumer は大半が docs / examples / archive 内リンクであり、runtime consumer は限定的である。benchmark baseline については `PR #2629`、verification snapshot については `PR #2632` で `artifacts/reference/*` へ移動済みである。

- `artifacts/reference/benchmarks/bench.json`: `src/commands/bench/run.ts`, benchmark schema tests, benchmark comparison docs/templates
- `artifacts/reference/benchmarks/bench.md`: benchmark human-readable report docs
- `artifacts/reference/verify/verify.md`: `src/commands/verify/run.ts`, archive 参照、notes 参照
- `artifacts/reference/types/types-gate-ci-validation.md`: notes 参照、layout docs 参照
- `artifacts/reference/types/types-hardening-validation.md`: notes 参照、layout docs 参照
- `artifacts/public-types.current.d.ts`: `scripts/api/check-types.mjs`, type hardening docs

このため、最初の実移動は **docs / tests / script output path** の更新を伴うが、branch protection や runtime contract への影響は限定的と見込む。

## Proposed PR Split
1. metadata-only inventory landing
   - inventory script
   - planning doc
   - issue comment / execution order
2. move root-level benchmark snapshots into `artifacts/reference/benchmarks/*`
   - completed in `PR #2629`
3. move verification snapshots into `artifacts/reference/verify/*`
   - completed in `PR #2632` (tracked by `Issue #2631`)
4. move type/reference snapshots into `artifacts/reference/types/*`
   - tracked under `Issue #2633`
5. move tracked hermetic / validation snapshots into `artifacts/reference/{hermetic-reports,validation-results}/**`

## Validation
- `pnpm run maintenance:artifact:inventory`
- `pnpm -s run check:doc-consistency`
- `pnpm -s run check:ci-doc-index-consistency`
