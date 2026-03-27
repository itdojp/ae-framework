---
docRole: derived
canonicalSource:
- docs/product/PRODUCT-FIT-INPUT-OUTPUT-TOOL-MAP.md
- docs/quality/verify-first-implementation-runbook.md
lastVerified: '2026-03-27'
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
   - average linked coverage across `testsLinked`, `implLinked`, and `formalLinked`
   - uses `coverage.tests|impl|formal` when those values are present
3. Automation
   - required-step pass rate from verify-profile summary (70%)
   - execution rate (`non-skipped steps / total steps`, 30%)
4. Quality Detection
   - whether failed runs are recorded in history
   - latest quality report score
   - run-manifest freshness result

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

- Run index: `artifacts/runs/index.json`
- Traceability: `traceability.json`
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

1. Reproducibility
   - run history の成功率（成功件数 / 総件数）
2. Traceability
   - `testsLinked` / `implLinked` / `formalLinked` の被覆率平均
   - `coverage.tests|impl|formal` がある場合はそれを利用
3. Automation
   - verify profile の required step pass rate（70%）
   - 実行率（non-skipped step / 全 step、30%）
4. Quality Detection
   - 失敗 run を履歴として記録できているか
   - quality report の最新スコア
   - run-manifest freshness チェック結果

overall score は利用可能な軸の単純平均です。

### CI向け終了コード契約

- `0`: レポート生成成功かつポリシー通過（`--min-score` 指定時は閾値達成を含む）
- `1`: ポリシー違反（例: `--min-score` 未達）
- `2`: 入力不正、引数不正、JSON parse失敗、または `--strict-inputs` 未充足

### `strict-inputs`

`--strict-inputs` を指定した場合、4軸のいずれかが算出不能なら exit `2` で失敗します。CI の fail-fast 用途では `--strict-inputs --min-score <threshold>` の併用を推奨します。
