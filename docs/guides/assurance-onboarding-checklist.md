# Assurance Onboarding Checklist

> Language / 言語: English | 日本語

---

## 日本語

新規プロジェクトへ assurance profile / summary / strict enforcement を導入するための最小チェックリストです。

### 前提条件
- Node.js: `>=20.11 <23`
- pnpm: `10.x`
- 実行場所: repository root
- 基本概念を `docs/quality/assurance-profile.md` と `docs/quality/assurance-lanes.md` で確認済み

### 0. framework 側の fixture で疎通確認

```bash
pnpm run verify:assurance \
  --assurance-profile fixtures/assurance/sample.assurance-profile.json \
  --context-pack fixtures/context-pack/sample.context-pack.json \
  --verify-lite-summary packages/envelope/__fixtures__/verify-lite-summary.json \
  --counterexample fixtures/counterexample/sample.counterexample.json \
  --evidence-manifest fixtures/assurance/sample.assurance-evidence-manifest.json \
  --output-json artifacts/assurance/assurance-summary.json \
  --output-md artifacts/assurance/assurance-summary.md
```

### 1. assurance profile を作成
- `schema/assurance-profile.schema.json` に従って project 固有 profile を作成する
- 各 claim に以下を定義する
  - `id`
  - `statement`
  - `criticality`
  - `targetLevel`
  - `requiredLanes`
  - `requiredEvidenceKinds`
  - `minIndependentSources`

### 2. Context Pack と claim ref を結ぶ
- Context Pack を使うプロジェクトでは `assurance.profile` と `claim_refs` を埋める
- claim ref は object / morphism / acceptance test と対応付く単位で最小に保つ

### 3. evidence source を揃える
- 最低限の候補:
  - `artifacts/verify-lite/verify-lite-run-summary.json`
  - `artifacts/formal/formal-summary-v1.json`
  - `artifacts/hermetic-reports/conformance/summary.json`
  - `fixtures/counterexample/*.json` または生成された counterexample JSON
  - `fixtures/assurance/*.json` 相当の supplemental evidence manifest
- claim ごとに required lanes と required evidence kinds を満たせる組み合わせを先に決める

### 4. report-only で導入する

```bash
pnpm run verify:lite
pnpm run verify:assurance \
  --assurance-profile path/to/assurance-profile.json \
  --verify-lite-summary artifacts/verify-lite/verify-lite-run-summary.json \
  --output-json artifacts/assurance/assurance-summary.json \
  --output-md artifacts/assurance/assurance-summary.md
node scripts/ci/validate-assurance-summary.mjs \
  artifacts/assurance/assurance-summary.json \
  schema/assurance-summary.schema.json
```

### 5. strict enforcement は high-risk PR のみ有効化
- 通常 PR は report-only のまま運用する
- `enforce-assurance` は high-risk change に限定する
- strict 運用前に `warningClaims == 0` を確認する

### 6. PR 前確認
- [ ] assurance profile が schema-valid
- [ ] `verify-lite` の summary を生成済み
- [ ] `verify:assurance` の summary を生成済み
- [ ] `missingLanes == []` を確認済み
- [ ] `missingEvidenceKinds == []` を確認済み
- [ ] `openCounterexamples == 0` を確認済み
- [ ] `enforce-assurance` を付ける場合、PR 本文または Issue に理由を記録した

### 7. 参照
- `docs/quality/assurance-operations-runbook.md`
- `docs/quality/assurance-profile.md`
- `docs/quality/assurance-lanes.md`
- `docs/quality/ARTIFACTS-CONTRACT.md`

---

## English

Minimal onboarding checklist for introducing assurance profile / summary / strict enforcement into a project.

See `docs/quality/assurance-operations-runbook.md` for operational details.
