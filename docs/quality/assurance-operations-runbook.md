# Assurance Operations Runbook

> Language / 言語: English | 日本語

---

## English (Summary)

Operational runbook for generating, validating, and enforcing `artifacts/assurance/assurance-summary.{json,md}` in ae-framework.

---

## 日本語

## 1. 目的

本 runbook は、現行実装の assurance 運用を 1 本に集約するための標準手順です。

対象:
- `pnpm run verify:assurance` のローカル実行
- `verify-lite.yml` における report-only 集約
- `enforce-assurance` ラベル時の strict enforcement
- `artifacts/assurance/assurance-summary.{json,md}` の読み方
- 失敗時の一次切り分け

## 2. 前提

- Node.js: `>=20.11 <23`
- pnpm: `10.x`
- 実行場所: repository root
- 入力契約を `docs/quality/assurance-profile.md` で確認済み
- lane taxonomy を `docs/quality/assurance-lanes.md` で確認済み

## 3. 入力と出力

### 3.1 主入力

| 種別 | パス例 | 必須 | 用途 |
| --- | --- | --- | --- |
| assurance profile | `fixtures/assurance/sample.assurance-profile.json` | 必須 | claim / required lanes / required evidence kinds |
| context pack | `fixtures/context-pack/sample.context-pack.json` | 任意 | claim と spec 参照の補完 |
| verify-lite summary | `artifacts/verify-lite/verify-lite-run-summary.json` | 任意 | behavior / spec / runtime の観測 |
| formal summary | `artifacts/formal/formal-summary-v1.json` | 任意 | model / proof lane の観測 |
| conformance report | `artifacts/hermetic-reports/conformance/summary.json` | 任意 | model lane の補完 |
| counterexample | `fixtures/counterexample/sample.counterexample.json` | 任意 | adversarial lane / triage 状態 |
| evidence manifest | `fixtures/assurance/sample.assurance-evidence-manifest.json` | 任意 | claim ごとの supplemental evidence |

### 3.2 主出力

| パス | 役割 |
| --- | --- |
| `artifacts/assurance/assurance-summary.json` | 機械可読 summary |
| `artifacts/assurance/assurance-summary.md` | 人間向け summary |

## 4. ローカル実行（report-only）

### Step 1: Verify Lite を実行して入力を揃える

```bash
pnpm run verify:lite
```

### Step 2: assurance summary を生成する

```bash
pnpm run verify:assurance \
  --assurance-profile fixtures/assurance/sample.assurance-profile.json \
  --verify-lite-summary artifacts/verify-lite/verify-lite-run-summary.json \
  --output-json artifacts/assurance/assurance-summary.json \
  --output-md artifacts/assurance/assurance-summary.md
```

追加の artifact を使う場合は、存在するファイルだけを渡します。

```bash
args=(
  --assurance-profile fixtures/assurance/sample.assurance-profile.json
  --verify-lite-summary artifacts/verify-lite/verify-lite-run-summary.json
  --output-json artifacts/assurance/assurance-summary.json
  --output-md artifacts/assurance/assurance-summary.md
)
if [ -f fixtures/context-pack/sample.context-pack.json ]; then
  args+=(--context-pack fixtures/context-pack/sample.context-pack.json)
fi
for formal_summary in artifacts/formal/formal-summary-v1.json artifacts/formal/formal-summary-v2.json; do
  if [ -f "$formal_summary" ]; then
    args+=(--formal-summary "$formal_summary")
  fi
done
if [ -f artifacts/hermetic-reports/conformance/summary.json ]; then
  args+=(--conformance-report artifacts/hermetic-reports/conformance/summary.json)
fi
if [ -f fixtures/counterexample/sample.counterexample.json ]; then
  args+=(--counterexample fixtures/counterexample/sample.counterexample.json)
fi
if [ -f fixtures/assurance/sample.assurance-evidence-manifest.json ]; then
  args+=(--evidence-manifest fixtures/assurance/sample.assurance-evidence-manifest.json)
fi
pnpm run verify:assurance "${args[@]}"
```

### Step 3: schema を検証する

```bash
node scripts/ci/validate-assurance-summary.mjs \
  artifacts/assurance/assurance-summary.json \
  schema/assurance-summary.schema.json
```

## 5. CI 運用

### 5.1 既定動作

- `verify-lite.yml` は assurance summary を report-only で生成します。
- PR summary comment は `artifacts/assurance/assurance-summary.json` が存在する場合に、claim summary を追記します。
- release/post-deploy summary は `artifacts/assurance/assurance-summary.md` が存在する場合に要約を追記します。

### 5.2 strict assurance enforcement の発火条件

- PR に `enforce-assurance` ラベルが付いている場合のみ、`verify-lite.yml` の `Enforce assurance summary (strict; label-gated)` ステップで strict assurance enforcement を有効化します。
- `pull_request` の `labeled` / `unlabeled` / `ready_for_review` で Verify Lite を再評価するため、ラベル操作後も同一 PR 上で再実行されます。

### 5.3 strict assurance enforcement のローカル再現

```bash
node scripts/ci/enforce-assurance-summary.mjs \
  artifacts/assurance/assurance-summary.json
```

strict assurance enforcement は少なくとも次を失敗条件として扱います。
- `summary.claimCount < 1`
- `summary.warningClaims > 0`
- `summary.warningCount > 0`
- `summary.claimsMissingRequiredLanes > 0`
- `summary.claimsMissingRequiredEvidenceKinds > 0`
- `summary.unlinkedCounterexamples > 0`
- 任意 claim の `status != satisfied`
- 任意 claim の `missingLanes` / `missingEvidenceKinds` / `independenceWarnings`
- 任意 claim の `counterexamples.open > 0`

## 6. summary の読み方

### 6.1 summary レベル

優先的に確認する項目:
- `claimCount`
- `warningClaims`
- `claimsMissingRequiredLanes`
- `claimsMissingRequiredEvidenceKinds`
- `unlinkedCounterexamples`
- `warningCount`

### 6.2 claim レベル

claim ごとに確認する項目:
- `status`
- `observedLanes`
- `missingLanes`
- `observedEvidenceKinds`
- `missingEvidenceKinds`
- `independenceWarnings`
- `counterexamples.open`

## 7. 失敗時の一次切り分け

### 7.1 `summary not found`

確認順:
1. `verify-lite` が完走しているか
2. `Aggregate assurance summary` step が実行されたか
3. `artifacts/assurance/assurance-summary.json` が生成されているか
4. `verify:assurance` の引数に `--assurance-profile` と `--output-json` が含まれているか

### 7.2 `missingLanes` / `missingEvidenceKinds`

確認順:
1. `docs/quality/assurance-profile.md` の claim 定義を確認
2. `assurance-summary.json` の該当 claim を確認
3. 不足 lane が formal / conformance / counterexample / evidence manifest のどれで埋まるかを判断
4. 入力 artifact を追加して `verify:assurance` を再実行

### 7.3 `openCounterexamples > 0` / `unlinkedCounterexamples > 0`

確認順:
1. `fixtures/counterexample/*.json` または生成された counterexample JSON を確認
2. `claimIds` / `morphismIds` / `triageStatus` / `replayCommand` を補完
3. `triageStatus=open` のまま strict に掛けていないかを確認

## 8. PR 前チェックリスト

- [ ] `pnpm run verify:lite` が通っている
- [ ] `pnpm run verify:assurance ...` の出力を確認した
- [ ] `artifacts/assurance/assurance-summary.json` が schema-valid である
- [ ] `enforce-assurance` を付ける理由を PR 本文または Issue に記録した
- [ ] strict 運用時に warning / open counterexample を残していない

## 9. 参照

- `docs/quality/assurance-profile.md`
- `docs/quality/assurance-lanes.md`
- `docs/quality/ARTIFACTS-CONTRACT.md`
- `docs/guides/assurance-onboarding-checklist.md`
- `scripts/assurance/aggregate-lanes.mjs`
- `scripts/ci/enforce-assurance-summary.mjs`
- `.github/workflows/verify-lite.yml`
