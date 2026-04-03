---
docRole: derived
canonicalSource:
- docs/quality/ARTIFACTS-CONTRACT.md
- docs/reference/CONTRACT-CATALOG.md
lastVerified: '2026-04-03'
---
# Run Manifest Freshness Contract

> Language / 言語: English | 日本語

---

## English

### 1. Purpose
Artifact presence alone does not prove freshness for the current commit. When a local run or partial rerun leaves old artifacts behind, CI or operator judgment can incorrectly treat them as valid evidence.

This contract defines how `run-manifest.json` records:
- the commit that produced each artifact, and
- whether that artifact is stale relative to the current commit.

The goal is to make freshness checks deterministic in both CI and local execution.

### 2. Generation
Generate the manifest with `node scripts/ci/generate-run-manifest.mjs`. By default it writes `artifacts/run-manifest.json`.

```bash
node scripts/ci/generate-run-manifest.mjs \
  --top-level-command "pnpm run verify:lite"
```

### 3. Validation
Validate the manifest with `node scripts/ci/check-run-manifest.mjs`.

```bash
node scripts/ci/check-run-manifest.mjs \
  --manifest artifacts/run-manifest.json \
  --require-fresh verifyLite,reportEnvelope,formal,formalSummaryV1 \
  --result artifacts/run-manifest-check.json
```

#### `--require-fresh`
For each named summary such as `verifyLite`, validation requires:
- `status == "present"`
- `staleComparedToCurrentCommit == false`

If `producedByCommit` cannot be extracted and `staleComparedToCurrentCommit == null`, the result is treated as `freshness_unknown` and the script records it as a violation. Higher-level workflows may still decide whether that failure is blocking or report-only.

### 4. Field overview
- `metadata.gitCommit`: current commit at manifest generation time
- `summaries.<name>.producedByCommit`: commit extracted from the artifact JSON on a best-effort basis
- `summaries.<name>.staleComparedToCurrentCommit`: comparison result between `producedByCommit` and `metadata.gitCommit`

### 5. References
- `schema/run-manifest.schema.json`
- `scripts/ci/generate-run-manifest.mjs`
- `scripts/ci/check-run-manifest.mjs`

---

## 日本語

### 1. 目的
成果物が「存在する」だけでは、**現コミットに対して最新（fresh）**である保証になりません。部分的な再実行やローカル検証で古い成果物が残っていると、誤って成功判定になるリスクがあります。

本契約は、`run-manifest.json` により成果物の **producedByCommit** と **staleComparedToCurrentCommit** を記録し、CI / ローカルの両方で鮮度違反を検出できるようにします。

### 2. 生成
`node scripts/ci/generate-run-manifest.mjs` を実行し、既定では `artifacts/run-manifest.json` を生成します。

```bash
node scripts/ci/generate-run-manifest.mjs \
  --top-level-command "pnpm run verify:lite"
```

### 3. 検証
`node scripts/ci/check-run-manifest.mjs` で検証します。

```bash
node scripts/ci/check-run-manifest.mjs \
  --manifest artifacts/run-manifest.json \
  --require-fresh verifyLite,reportEnvelope,formal,formalSummaryV1 \
  --result artifacts/run-manifest-check.json
```

#### `--require-fresh`
指定した名前（例: `verifyLite`）について、以下を必須化します。
- `status == "present"`
- `staleComparedToCurrentCommit == false`

`producedByCommit` が取得できず `staleComparedToCurrentCommit == null` の場合は **freshness_unknown** として違反を記録します。上位の workflow や運用レイヤーでは、その結果を blocking と扱うか report-only と扱うかを別途判断できます。

### 4. フィールド概要
- `metadata.gitCommit`: 現在のコミット（マニフェスト生成時点）
- `summaries.<name>.producedByCommit`: 成果物 JSON 内部から抽出したコミット（best-effort）
- `summaries.<name>.staleComparedToCurrentCommit`: `producedByCommit` と `metadata.gitCommit` の比較結果

### 5. 参照
- `schema/run-manifest.schema.json`
- `scripts/ci/generate-run-manifest.mjs`
- `scripts/ci/check-run-manifest.mjs`
