# Artifacts/Reports 契約（Required / Optional）

> Language / 言語: English | 日本語

---

## English (Summary)

Defines required vs optional artifacts and how to validate them in CI.

---

## 日本語

## 1. 目的
CIが生成する成果物（artifacts/reports）について **最低限の契約（contract）** を定義し、missing/invalid を早期に検出できるようにします。

### 1.1 用語の注記
- 本ドキュメントでの contract は **Artifacts contract**（成果物の必須/任意ルール）を指します。
- DbC（Design contract: pre/post/invariant）や API/Integration contract（Pact）とは別概念です。
- 用語の基準は `docs/quality/contract-taxonomy.md` を参照してください。

## 2. Required（必須）成果物

| 成果物 | 生成元 | 検証 | 備考 |
| --- | --- | --- | --- |
| `artifacts/verify-lite/verify-lite-run-summary.json` | `pnpm run verify:lite` | JSON parse + schema | verify-lite の要約 |
| `artifacts/report-envelope.json` | `scripts/trace/create-report-envelope.mjs` | JSON parse + schema | verify-lite で生成されるレポート封筒 |

> スキーマ検証は既に `verify-lite.yml` に含まれています。  
> 本ドキュメントは「**存在と最低限の整合性**」を必須化する目的です。

### 成果物メタデータ（共通）
- `artifacts/verify-lite/verify-lite-run-summary.json` と `formal/summary.json` には `metadata` を付与します。
- 共通スキーマ: `schema/artifact-metadata.schema.json`
- 主要フィールド: `generatedAtUtc`, `generatedAtLocal`, `timezoneOffset`, `gitCommit`, `branch`, `runner`, `toolVersions`

## 3. Optional（条件付き）成果物

| 成果物 | 条件 | 備考 |
| --- | --- | --- |
| `artifacts/hermetic-reports/conformance/summary.json` | conformance 検証を実行した場合 | `verify-conformance.mjs` の出力 |
| `artifacts/hermetic-reports/formal/summary.json` | formal aggregate を実行した場合 | `aggregate-formal.mjs` の出力 |
| `artifacts/hermetic-reports/formal/*-output.txt` | formal verifier を実行した場合 | 各ツールの実行ログ（全文）。Formal Summary v1 の `results[].logPath` から参照される場合があります |
| `artifacts/formal/formal-summary-v1.json` | formal aggregate または verify-lite（`run-formal`）を実行した場合 | Formal Summary v1（normalized、スキーマ: `schema/formal-summary-v1.schema.json`） |
| `artifacts/context-pack/context-pack-functor-report.json` | context-pack functor 検証を実行した場合 | `scripts/context-pack/verify-functor.mjs` の JSON レポート（違反種別・対象 object/morphism を含む） |
| `artifacts/context-pack/context-pack-functor-report.md` | context-pack functor 検証を実行した場合 | `scripts/context-pack/verify-functor.mjs` の Markdown 要約 |
| `artifacts/context-pack/context-pack-natural-transformation-report.json` | context-pack natural transformation 検証を実行した場合 | `scripts/context-pack/verify-natural-transformation.mjs` の JSON レポート（可換チェック/禁止変更連携の違反種別を含む） |
| `artifacts/context-pack/context-pack-natural-transformation-report.md` | context-pack natural transformation 検証を実行した場合 | `scripts/context-pack/verify-natural-transformation.mjs` の Markdown 要約 |
| `artifacts/context-pack/context-pack-product-coproduct-report.json` | context-pack product/coproduct 検証を実行した場合 | `scripts/context-pack/verify-product-coproduct.mjs` の JSON レポート（入力必須項目/失敗variant網羅/証跡不足を含む） |
| `artifacts/context-pack/context-pack-product-coproduct-report.md` | context-pack product/coproduct 検証を実行した場合 | `scripts/context-pack/verify-product-coproduct.mjs` の Markdown 要約 |

## 4. 検証スクリプト

```bash
# 既定の必須成果物を確認（非厳格）
node scripts/ci/check-required-artifacts.mjs

# 必須成果物を明示して厳格チェック
REQUIRED_ARTIFACTS=artifacts/verify-lite/verify-lite-run-summary.json,artifacts/report-envelope.json \
REQUIRED_ARTIFACTS_STRICT=1 \
node scripts/ci/check-required-artifacts.mjs --strict
```

## 5. CI統合（段階導入）
- `verify-lite.yml` に **non-blocking** で組み込み（観測フェーズ）
- 厳格化する場合は `REQUIRED_ARTIFACTS_STRICT=1` を有効化  
  - 例: PRラベル `enforce-artifacts` を条件に strict モードを有効化
- `verify-lite.yml` の必須ステップで `tests/contracts/cli-artifacts-contracts.test.ts` を実行し、主要CLIの JSON schema / exit code 契約を継続検証

## 6. 参照
- `.github/workflows/verify-lite.yml`
- `.github/workflows/formal-aggregate.yml`
- `.github/workflows/formal-verify.yml`
- `scripts/ci/check-required-artifacts.mjs`
- `scripts/ci/validate-formal-summary-v1.mjs`
- `schema/artifact-metadata.schema.json`
- `schema/formal-summary-v1.schema.json`
- `docs/quality/path-normalization-contract.md`
- `docs/quality/run-manifest-freshness-contract.md`
