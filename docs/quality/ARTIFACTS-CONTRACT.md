# Artifacts/Reports 契約（Required / Optional）

> Language / 言語: English | 日本語

---

## English (Summary)

Defines required vs optional artifacts and how to validate them in CI.

---

## 日本語

## 1. 目的
CIが生成する成果物（artifacts/reports）について **最低限の契約（contract）** を定義し、\nmissing/invalid を早期に検出できるようにします。

## 2. Required（必須）成果物

| 成果物 | 生成元 | 検証 | 備考 |
| --- | --- | --- | --- |
| `artifacts/verify-lite/verify-lite-run-summary.json` | `pnpm run verify:lite` | JSON parse + schema | verify-lite の要約 |
| `artifacts/report-envelope.json` | `scripts/trace/create-report-envelope.mjs` | JSON parse + schema | verify-lite で生成されるレポート封筒 |

> スキーマ検証は既に `verify-lite.yml` に含まれています。  
> 本ドキュメントは「**存在と最低限の整合性**」を必須化する目的です。

## 3. Optional（条件付き）成果物

| 成果物 | 条件 | 備考 |
| --- | --- | --- |
| `artifacts/hermetic-reports/conformance/summary.json` | conformance 検証を実行した場合 | `verify-conformance.mjs` の出力 |
| `artifacts/hermetic-reports/formal/summary.json` | formal aggregate を実行した場合 | `aggregate-formal.mjs` の出力 |

## 4. 検証スクリプト

```bash
# 既定の必須成果物を確認（非厳格）
node scripts/ci/check-required-artifacts.mjs

# 必須成果物を明示して厳格チェック
REQUIRED_ARTIFACTS=artifacts/verify-lite/verify-lite-run-summary.json,artifacts/report-envelope.json \\
REQUIRED_ARTIFACTS_STRICT=1 \\
node scripts/ci/check-required-artifacts.mjs --strict
```

## 5. CI統合（段階導入）
- `verify-lite.yml` に **non-blocking** で組み込み（観測フェーズ）
- 厳格化する場合は `REQUIRED_ARTIFACTS_STRICT=1` を有効化  
  - 例: PRラベル `enforce-artifacts` を条件に strict モードを有効化

## 6. 参照
- `.github/workflows/verify-lite.yml`
- `scripts/ci/check-required-artifacts.mjs`
