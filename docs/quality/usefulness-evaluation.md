# Usefulness Evaluation Report

`evaluate:usefulness` は、ae-framework 導入効果を 4 軸で定量化し、JSON/Markdown でレポート化する標準コマンドです。

## コマンド

```bash
pnpm run evaluate:usefulness
pnpm run evaluate:usefulness -- --strict-inputs --min-score 70
```

## 入力（既定パス）

- Run index: `artifacts/runs/index.json`
- Traceability: `traceability.json`
- Verify profile summary: `artifacts/verify-profile-summary.json`
- Quality report: `reports/quality-gates/quality-report-ci-latest.json`
- Run manifest check: `artifacts/run-manifest-check.json`

必要に応じて `--run-index` / `--traceability` / `--verify-profile` / `--quality-report` / `--run-manifest-check` で上書き可能です。

## 出力

- JSON: `artifacts/evaluation/ae-framework-usefulness-latest.json`
- Markdown: `artifacts/evaluation/ae-framework-usefulness-latest.md`
- JSON schema: `schema/usefulness-evaluation-report.schema.json`

## 4軸の算出規約（v1）

1. Reproducibility  
   - run history の成功率（成功件数 / 総件数）

2. Traceability  
   - `testsLinked` / `implLinked` / `formalLinked` の被覆率平均  
   - `coverage.tests|impl|formal` がある場合はそれを利用

3. Automation  
   - verify profile の required step pass rate（70%）  
   - 実行率（non-skipped step / 全step、30%）

4. Quality Detection  
   - 失敗履歴シグナル（失敗 run を記録できているか）  
   - quality report の最新スコア  
   - run-manifest freshness チェック結果

overall score は利用可能な軸の単純平均です。

## CI向け終了コード契約

- `0`: レポート生成成功（かつ `--min-score` を満たす）
- `1`: ポリシー違反（例: `--min-score` 未達）
- `2`: 入力不正（引数不正 / JSON parse失敗 / `--strict-inputs` 未充足）

## strict-inputs

`--strict-inputs` を指定した場合、4軸のいずれかが算出不能なら exit 2 で失敗します。  
CI の fail-fast 用途では `--strict-inputs --min-score <threshold>` の併用を推奨します。
