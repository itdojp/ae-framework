---
docRole: derived
canonicalSource:
- docs/product/PRODUCT-FIT-INPUT-OUTPUT-TOOL-MAP.md
- docs/quality/verify-first-implementation-runbook.md
lastVerified: '2026-04-07'
---
# Usefulness Evaluation Report

> Language / 言語: English | 日本語

---

## English

`evaluate:usefulness` is the standard command that quantifies ae-framework adoption value across four axes and writes both JSON and Markdown reports.

### Command

```bash
pnpm run evaluate:usefulness
pnpm run evaluate:usefulness -- --strict-inputs --min-score 70
```

### Default inputs

- Run index: `artifacts/runs/index.json`
- Traceability: `traceability.json`
- Verify profile summary: `artifacts/verify-profile-summary.json`
- Quality report: `reports/quality-gates/quality-report-ci-latest.json`
- Run manifest check: `artifacts/run-manifest-check.json`

Override these with `--run-index`, `--traceability`, `--verify-profile`, `--quality-report`, and `--run-manifest-check` when the defaults do not match the current workspace or CI artifact layout.

### Outputs

- JSON: `artifacts/evaluation/ae-framework-usefulness-latest.json`
- Markdown: `artifacts/evaluation/ae-framework-usefulness-latest.md`
- JSON schema: `schema/usefulness-evaluation-report.schema.json`
- `schemaVersion`: `usefulness-evaluation/v1`

### Axis scoring rules (v1)

1. Reproducibility
   - success rate from run history (`successes / total runs`)
2. Traceability
   - primary metric: average linked coverage across `testsLinked`, `implLinked`, and `formalLinked`
   - if linked coverage ratios cannot be calculated from `total` and `*Linked`, falls back to `coverage.tests|impl|formal` when those values are present
3. Automation
   - required-step pass rate from verify-profile summary (70%)
   - execution rate (`non-skipped steps / total steps`, 30%)
4. Quality Detection
   - base signal from run history: score `100` when at least one failed run is recorded, otherwise `70`
   - averages the base signal with the latest quality report score and the run-manifest freshness score when those signals are available
   - if quality report and run-manifest signals are both missing, falls back to the latest-run heuristic: `85` for success, `35` for failure

The overall score is the simple average of available axes.

### CI exit contract

- `0`: report generation succeeded and the policy passed, including `--min-score` when provided
- `1`: policy violation, for example `--min-score` not met
- `2`: invalid input, argument error, JSON parse error, or `--strict-inputs` violation

### `strict-inputs`

When `--strict-inputs` is enabled, the command exits with `2` if any of the four axes cannot be calculated. For fail-fast CI usage, combine `--strict-inputs` with `--min-score <threshold>`.

## 日本語

`evaluate:usefulness` は、ae-framework 導入効果を 4 軸で定量化し、JSON/Markdown でレポート化する標準コマンドです。

### コマンド

```bash
pnpm run evaluate:usefulness
pnpm run evaluate:usefulness -- --strict-inputs --min-score 70
```

### 入力（既定パス）

- 実行インデックス（Run index）: `artifacts/runs/index.json`
- トレーサビリティ（Traceability）: `traceability.json`
- Verify profile summary: `artifacts/verify-profile-summary.json`
- Quality report: `reports/quality-gates/quality-report-ci-latest.json`
- Run manifest check: `artifacts/run-manifest-check.json`

必要に応じて `--run-index` / `--traceability` / `--verify-profile` / `--quality-report` / `--run-manifest-check` で上書き可能です。

### 出力

- JSON: `artifacts/evaluation/ae-framework-usefulness-latest.json`
- Markdown: `artifacts/evaluation/ae-framework-usefulness-latest.md`
- JSON schema: `schema/usefulness-evaluation-report.schema.json`
- `schemaVersion`: `usefulness-evaluation/v1`

### 4軸の算出規約（v1）

1. 再現性（Reproducibility）
   - run history の成功率（成功件数 / 総件数）
2. トレーサビリティ（Traceability）
   - `testsLinked` / `implLinked` / `formalLinked` の被覆率平均を主指標として利用
   - `total` と `*Linked` から被覆率を算出できない場合に限り `coverage.tests|impl|formal` をフォールバックとして利用
3. 自動化（Automation）
   - verify profile の required step pass rate（70%）
   - 実行率（non-skipped step / 全 step、30%）
4. 品質検知（Quality Detection）
   - run history に失敗が 1 件以上含まれていれば `100`、含まれなければ `70` をベーススコアとする
   - ベーススコアと quality report の最新スコア、run-manifest freshness のスコアがあればそれらを平均する
   - quality report / run-manifest のシグナルがどちらも無い場合は latest run の成否により `85`（成功）/ `35`（失敗）でフォールバックする

総合スコア（overall score）は利用可能な軸の単純平均です。

### CI向け終了コード契約

- `0`: レポート生成成功かつポリシー通過（`--min-score` 指定時は閾値達成を含む）
- `1`: ポリシー違反（例: `--min-score` 未達）
- `2`: 入力不正、引数不正、JSON parse 失敗、または `--strict-inputs` 未充足

### `strict-inputs`

`--strict-inputs` を指定した場合、4軸のいずれかが算出不能なら exit `2` で失敗します。CI の fail-fast 用途では `--strict-inputs --min-score <threshold>` の併用を推奨します。
