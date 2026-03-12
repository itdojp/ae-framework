---
docRole: narrative
lastVerified: '2026-03-12'
owner: repo-maintenance
verificationCommand: pnpm run maintenance:artifact:inventory
---
# Artifact Reference Layout Plan

## Summary
`artifacts/` は `repo-layout-policy` 上では 5 類型に整理されているが、本メモの対象となる tracked artifact はそのうち 4 類型である。reference snapshot の実移動は完了しており、本メモの残件は runtime output namespace に残った tracked placeholder の扱いだけである。

この文書は `Issue #2585` の planning memo として、tracked artifact inventory と小粒 PR の投入順を定義する。

## Current Inventory
`pnpm run maintenance:artifact:inventory` の最新出力では、tracked artifact は以下に分類される。

- committed contract artifact: `artifacts/types/**`, `artifacts/contracts/**`, `artifacts/domain/**`, `artifacts/plan/**`, `artifacts/api/**`, `artifacts/bdd/**`, `artifacts/properties/**`, `artifacts/repros/**`
- reference snapshot: `artifacts/reference/benchmarks/*`, `artifacts/reference/verify/*`, `artifacts/reference/types/*`, `artifacts/reference/validation-results/*`, `artifacts/reference/hermetic-reports/formal/*`, `artifacts/reference/hermetic-reports/*.md`
- archive: `artifacts/archive/**`
- local debug archive: `artifacts/codex/**`

## Proposed Normalization
### Keep in place
- `artifacts/types/**`, `artifacts/contracts/**`, `artifacts/domain/**`, `artifacts/plan/**`, `artifacts/api/**`, `artifacts/bdd/**`, `artifacts/properties/**`, `artifacts/repros/**`
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
  - `artifacts/reference/types/public-types.current.d.ts`
  - status: normalization tracked under `Issue #2633` and `Issue #2642`

### Move to `artifacts/reference/**`
- hermetic snapshots
  - formal tracked summary: `artifacts/reference/hermetic-reports/formal/*`
    - status: normalized in `PR #2639` (tracked by `Issue #2638`)
  - tracked markdown snapshot: `artifacts/reference/hermetic-reports/*.md`
    - status: normalized in `PR #2641` (tracked by `Issue #2640`)

### Runtime output namespace policy
- `artifacts/hermetic-reports/.gitkeep` は追跡しない
  - rationale: formal / trace scripts と workflows が `mkdir -p` / recursive mkdir で必要なサブディレクトリを都度生成する
  - tracked reference snapshot は `artifacts/reference/hermetic-reports/**` に集約済み

## Consumer Impact
現時点の root-level tracked snapshot の consumer は大半が docs / examples / archive 内リンクであり、runtime consumer は限定的である。benchmark baseline については `PR #2629`、verification snapshot については `PR #2632` で `artifacts/reference/*` へ移動済みである。

- `artifacts/reference/benchmarks/bench.json`: `src/commands/bench/run.ts`, benchmark schema tests, benchmark comparison docs/templates
- `artifacts/reference/benchmarks/bench.md`: benchmark human-readable report docs
- `artifacts/reference/verify/verify.md`: `src/commands/verify/run.ts`, archive 参照、notes 参照
- `artifacts/reference/types/types-gate-ci-validation.md`: notes 参照、layout docs 参照
- `artifacts/reference/types/types-hardening-validation.md`: notes 参照、layout docs 参照
- `artifacts/reference/types/public-types.current.d.ts`: `scripts/api/check-types.mjs`, type hardening docs
- `artifacts/reference/validation-results/summary.json`: spec validation docs と inventory 参照。runtime output は `scripts/validate-specs.sh` が `artifacts/validation-results/` を継続利用
- `artifacts/reference/hermetic-reports/formal/*.json`: tracked formal baseline。runtime output は formal / trace scripts が `artifacts/hermetic-reports/**` を継続利用
- `artifacts/reference/hermetic-reports/*.md`: historical hermetic reference snapshot。runtime output は `artifacts/hermetic-reports/**` を継続利用

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
   - `types-gate-ci-validation.md` / `types-hardening-validation.md` completed in `PR #2634` (tracked by `Issue #2633`)
   - `public-types.current.d.ts` tracked under `Issue #2642`
5. move tracked validation snapshots into `artifacts/reference/validation-results/**`
   - completed in `PR #2637` (tracked by `Issue #2636`)
6. move tracked formal hermetic snapshots into `artifacts/reference/hermetic-reports/formal/*`
   - completed in `PR #2639` (tracked by `Issue #2638`)
7. move tracked top-level hermetic markdown snapshots into `artifacts/reference/hermetic-reports/*`
   - completed in `PR #2641` (tracked by `Issue #2640`)
8. remove tracked `.gitkeep` placeholder under `artifacts/hermetic-reports/` and document on-demand directory creation
   - completed in `Issue #2644`

## Validation
- `pnpm run maintenance:artifact:inventory`
- `pnpm -s run check:doc-consistency`
- `pnpm -s run check:ci-doc-index-consistency`
