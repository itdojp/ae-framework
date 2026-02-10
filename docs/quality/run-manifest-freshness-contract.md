# Run Manifest Freshness Contract

> Language / 言語: English | 日本語

---

## English (Summary)

Defines how to generate and check a `run-manifest.json` to detect stale artifacts (artifacts that exist but were produced for a different commit).

---

## 日本語

## 1. 目的
成果物が「存在する」だけでは、**現コミットに対して最新（fresh）**である保証になりません。部分的な再実行やローカル検証で古い成果物が残っていると、誤って成功判定になるリスクがあります。

本契約は、`run-manifest.json` により成果物の **producedByCommit** と **staleComparedToCurrentCommit** を記録し、CI/ローカルの両方で鮮度違反を検出できるようにします。

## 2. 生成（generate）
`node scripts/ci/generate-run-manifest.mjs` を実行し、既定では `artifacts/run-manifest.json` を生成します。

```bash
node scripts/ci/generate-run-manifest.mjs \
  --top-level-command "pnpm run verify:lite"
```

## 3. 検証（check）
`node scripts/ci/check-run-manifest.mjs` で検証します。

```bash
node scripts/ci/check-run-manifest.mjs \
  --manifest artifacts/run-manifest.json \
  --require-fresh verifyLite,reportEnvelope,formal,formalSummaryV1 \
  --result artifacts/run-manifest-check.json
```

### `--require-fresh`
指定した名前（例: `verifyLite`）について、以下を必須化します。
- `status == "present"`
- `staleComparedToCurrentCommit == false`

`producedByCommit` が取れず `staleComparedToCurrentCommit == null` の場合は **freshness_unknown** として失敗扱いにします（strict）。

## 4. フィールド概要
- `metadata.gitCommit`: 現在のコミット（マニフェスト生成時点）
- `summaries.<name>.producedByCommit`: 成果物JSON内部から抽出したコミット（best-effort）
- `summaries.<name>.staleComparedToCurrentCommit`: `producedByCommit` と `metadata.gitCommit` の比較結果（best-effort）

## 5. 参照
- `schema/run-manifest.schema.json`
- `scripts/ci/generate-run-manifest.mjs`
- `scripts/ci/check-run-manifest.mjs`
