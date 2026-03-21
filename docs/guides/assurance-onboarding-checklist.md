---
docRole: derived
canonicalSource:
- docs/quality/assurance-operations-runbook.md
- docs/quality/assurance-profile.md
lastVerified: '2026-03-21'
---
# Assurance Onboarding Checklist

> Language / 言語: English | 日本語

---

## 日本語

新規プロジェクトへ assurance profile / summary / strict assurance enforcement を導入するための最小チェックリストです。

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

### 5. strict assurance enforcement は high-risk PR のみ有効化
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

Minimal onboarding checklist for introducing assurance profile, assurance summary, and strict assurance enforcement into a project.

### Preconditions
- Node.js: `>=20.11 <23`
- pnpm: `10.x`
- run from the repository root
- review `docs/quality/assurance-profile.md` and `docs/quality/assurance-lanes.md` first

### 0. Smoke-test with framework fixtures

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

### 1. Create the assurance profile
- create a project-specific profile that follows `schema/assurance-profile.schema.json`
- define at least the following for each claim:
  - `id`
  - `statement`
  - `criticality`
  - `targetLevel`
  - `requiredLanes`
  - `requiredEvidenceKinds`
  - `minIndependentSources`

### 2. Link Context Pack and claim refs
- if the project uses Context Pack, populate `assurance.profile` and `claim_refs`
- keep each claim ref scoped to the smallest unit that maps cleanly to an object, morphism, or acceptance test

### 3. Prepare evidence sources
- minimum candidates:
  - `artifacts/verify-lite/verify-lite-run-summary.json`
  - `artifacts/formal/formal-summary-v1.json`
  - `artifacts/hermetic-reports/conformance/summary.json`
  - `fixtures/counterexample/*.json` or generated counterexample JSON
  - supplemental evidence manifests equivalent to `fixtures/assurance/*.json`
- decide upfront which combination satisfies each claim’s required lanes and evidence kinds

### 4. Start in report-only mode

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

### 5. Use strict assurance enforcement only for high-risk PRs
- keep standard PRs in report-only mode
- restrict `enforce-assurance` to high-risk changes
- confirm `warningClaims == 0` before enabling strict mode

### 6. Pre-PR checks
- [ ] the assurance profile is schema-valid
- [ ] `verify-lite` summary has been generated
- [ ] `verify:assurance` summary has been generated
- [ ] `missingLanes == []`
- [ ] `missingEvidenceKinds == []`
- [ ] `openCounterexamples == 0`
- [ ] if `enforce-assurance` is used, record the reason in the PR body or linked Issue

### 7. References
- `docs/quality/assurance-operations-runbook.md`
- `docs/quality/assurance-profile.md`
- `docs/quality/assurance-lanes.md`
- `docs/quality/ARTIFACTS-CONTRACT.md`
