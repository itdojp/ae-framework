---
docRole: derived
canonicalSource:
- docs/quality/ASSURANCE-MODEL.md
- docs/quality/ARTIFACTS-CONTRACT.md
lastVerified: '2026-04-03'
---
# Assurance Operations Runbook

> Language / 言語: English | 日本語

---

## English

### 1. Purpose

This runbook is the standard operating procedure for current assurance handling on `main`.

Scope:
- local execution of `pnpm run verify:assurance`
- report-only aggregation in `verify-lite.yml`
- strict assurance enforcement when the `enforce-assurance` label is present
- interpretation of `artifacts/assurance/assurance-summary.{json,md}`
- first-pass failure triage

### 2. Preconditions

- Node.js: `>=20.11 <23`
- pnpm: `10.x`
- run from the repository root
- review `docs/quality/assurance-profile.md` for the input contract
- review `docs/quality/assurance-lanes.md` for lane taxonomy

### 3. Inputs and outputs

#### 3.1 primary inputs

| kind | example path | required | purpose |
| --- | --- | --- | --- |
| assurance profile | `fixtures/assurance/sample.assurance-profile.json` | required | claims, required lanes, required evidence kinds |
| context pack | `fixtures/context-pack/sample.context-pack.json` | optional | supplements claim-to-spec references |
| verify-lite summary | `artifacts/verify-lite/verify-lite-run-summary.json` | optional | behavior, spec, and runtime observations |
| formal summary | `artifacts/formal/formal-summary-v2.json` (preferred) or `artifacts/formal/formal-summary-v1.json` | optional | model and proof observations |
| conformance report | `artifacts/hermetic-reports/conformance/summary.json` | optional | additional model-lane evidence |
| counterexample | `fixtures/counterexample/sample.counterexample.json` | optional | adversarial lane and triage state |
| evidence manifest | `fixtures/assurance/sample.assurance-evidence-manifest.json` | optional | supplemental evidence per claim |

#### 3.2 primary outputs

| path | role |
| --- | --- |
| `artifacts/assurance/assurance-summary.json` | machine-readable summary |
| `artifacts/assurance/assurance-summary.md` | human-readable summary |

### 4. Local execution (report-only)

#### Step 1: prepare inputs with Verify Lite

```bash
pnpm run verify:lite
```

#### Step 2: generate the assurance summary

```bash
pnpm run verify:assurance \
  --assurance-profile fixtures/assurance/sample.assurance-profile.json \
  --verify-lite-summary artifacts/verify-lite/verify-lite-run-summary.json \
  --output-json artifacts/assurance/assurance-summary.json \
  --output-md artifacts/assurance/assurance-summary.md
```

When extra artifacts are available, pass only the files that exist.

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

#### Step 3: validate the schema

```bash
node scripts/ci/validate-assurance-summary.mjs \
  artifacts/assurance/assurance-summary.json \
  schema/assurance-summary.schema.json
```

### 5. CI operation

#### 5.1 default behavior

- `verify-lite.yml` generates assurance summary in report-only mode.
- When `artifacts/assurance/assurance-summary.json` exists, `verify-lite.yml` also treats it as an optional input for `artifacts/quality/quality-scorecard.{json,md}`.
- `pr-ci-status-comment.yml` assembles the PR summary comment from harness-health, change-package, hook-feedback, and the downloaded `artifacts/quality/quality-scorecard.md`. When a verify-lite artifact for the same head SHA is available, it also passes `--assurance-summary` into hook-feedback generation. Assurance signals therefore appear through hook-feedback and the quality scorecard rather than by appending `artifacts/assurance/assurance-summary.md` or per-claim details directly.
- `pnpm run handoff:create` / `scripts/agents/create-handoff.mjs` consume `--assurance-summary` and reflect assurance warnings in `currentStatus`, `nextActions`, `blockers`, and `artifacts`.
- release and post-deploy summaries append a short summary when `artifacts/assurance/assurance-summary.md` exists.

#### 5.2 trigger for strict assurance enforcement

- Strict mode is enabled only when the PR carries the `enforce-assurance` label.
- `verify-lite.yml` reevaluates on `labeled`, `unlabeled`, and `ready_for_review`, so label changes are reflected on the same PR.

#### 5.3 local reproduction of strict assurance enforcement

```bash
node scripts/ci/enforce-assurance-summary.mjs \
  artifacts/assurance/assurance-summary.json
```

Strict enforcement treats at least the following as failures:
- `summary.claimCount < 1`
- `summary.warningClaims > 0`
- `summary.warningCount > 0`
- `summary.claimsMissingRequiredLanes > 0`
- `summary.claimsMissingRequiredEvidenceKinds > 0`
- `summary.unlinkedCounterexamples > 0`
- any claim with `status != satisfied`
- any claim with non-empty `missingLanes`, `missingEvidenceKinds`, or `independenceWarnings`
- any claim with `counterexamples.open > 0`

### 6. How to read the summary

#### 6.1 summary level

Check these fields first:
- `claimCount`
- `warningClaims`
- `claimsMissingRequiredLanes`
- `claimsMissingRequiredEvidenceKinds`
- `unlinkedCounterexamples`
- `warningCount`

#### 6.2 claim level

Check these fields per claim:
- `status`
- `observedLanes`
- `missingLanes`
- `observedEvidenceKinds`
- `missingEvidenceKinds`
- `independenceWarnings`
- `counterexamples.open`

### 7. First-pass triage

#### 7.1 `summary not found`

Check in this order:
1. whether `verify-lite` completed
2. whether the `Aggregate assurance summary` step executed
3. whether `artifacts/assurance/assurance-summary.json` exists
4. whether `verify:assurance` includes `--assurance-profile` and `--output-json`

#### 7.2 `missingLanes` / `missingEvidenceKinds`

Check in this order:
1. review claim definitions in `docs/quality/assurance-profile.md`
2. inspect the corresponding claim in `assurance-summary.json`
3. determine whether the missing lane can be filled by formal, conformance, counterexample, or evidence manifest inputs
4. add the missing artifact and rerun `verify:assurance`

#### 7.3 `openCounterexamples > 0` / `unlinkedCounterexamples > 0`

Check in this order:
1. inspect `fixtures/counterexample/*.json` or the generated counterexample JSON
2. complete `claimIds`, `morphismIds`, `triageStatus`, and `replayCommand`
3. confirm that strict mode is not being triggered while `triageStatus=open`

### 8. Pre-PR checklist

- [ ] `pnpm run verify:lite` succeeds
- [ ] review the output of `pnpm run verify:assurance ...`
- [ ] `artifacts/assurance/assurance-summary.json` is schema-valid
- [ ] record the reason for `enforce-assurance` in the PR body or linked Issue when the label is used
- [ ] do not leave warnings or open counterexamples before strict runs

### 9. References

- `docs/quality/assurance-profile.md`
- `docs/quality/assurance-lanes.md`
- `docs/quality/ARTIFACTS-CONTRACT.md`
- `docs/guides/assurance-onboarding-checklist.md`
- `scripts/assurance/aggregate-lanes.mjs`
- `scripts/ci/enforce-assurance-summary.mjs`
- `.github/workflows/verify-lite.yml`

---

## 日本語

### 1. 目的

本 runbook は、現行実装の assurance 運用を 1 本に集約するための標準手順です。

対象:
- `pnpm run verify:assurance` のローカル実行
- `verify-lite.yml` における report-only 集約
- `enforce-assurance` ラベル時の strict assurance enforcement
- `artifacts/assurance/assurance-summary.{json,md}` の読み方
- 失敗時の一次切り分け

### 2. 前提

- Node.js: `>=20.11 <23`
- pnpm: `10.x`
- 実行場所: リポジトリルート
- 入力契約を `docs/quality/assurance-profile.md` で確認済み
- 検証レーン taxonomy を `docs/quality/assurance-lanes.md` で確認済み

### 3. 入力と出力

### 3.1 主入力

| 種別 | パス例 | 必須 | 用途 |
| --- | --- | --- | --- |
| assurance profile | `fixtures/assurance/sample.assurance-profile.json` | 必須 | claim / required lanes / required evidence kinds |
| context pack | `fixtures/context-pack/sample.context-pack.json` | 任意 | claim と spec 参照の補完 |
| verify-lite summary | `artifacts/verify-lite/verify-lite-run-summary.json` | 任意 | behavior / spec / runtime の観測 |
| formal summary | `artifacts/formal/formal-summary-v2.json`（優先）または `artifacts/formal/formal-summary-v1.json` | 任意 | model / proof lane の観測 |
| conformance report | `artifacts/hermetic-reports/conformance/summary.json` | 任意 | model lane の補完 |
| counterexample | `fixtures/counterexample/sample.counterexample.json` | 任意 | adversarial lane / triage 状態 |
| evidence manifest | `fixtures/assurance/sample.assurance-evidence-manifest.json` | 任意 | claim ごとの supplemental evidence |

### 3.2 主出力

| パス | 役割 |
| --- | --- |
| `artifacts/assurance/assurance-summary.json` | 機械可読サマリー |
| `artifacts/assurance/assurance-summary.md` | 人間向けサマリー |

### 4. ローカル実行（report-only）

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

### 5. CI 運用

### 5.1 既定動作

- `verify-lite.yml` は assurance summary を report-only で生成します。
- `verify-lite.yml` は `artifacts/assurance/assurance-summary.json` が存在する場合、`artifacts/quality/quality-scorecard.{json,md}` の optional input としても利用します。
- `pr-ci-status-comment.yml` は harness-health / change-package / hook-feedback / downloaded `artifacts/quality/quality-scorecard.md` を組み合わせて PR summary comment を構成します。同一 head SHA の verify-lite artifact を取得できる場合は `hook-feedback` 生成時にも `--assurance-summary` を渡します。assurance の信号は `hook-feedback` と quality scorecard 経由で反映され、`artifacts/assurance/assurance-summary.md` や claim 単位の詳細を直接追記するわけではありません。
- `pnpm run handoff:create` / `scripts/agents/create-handoff.mjs` は `--assurance-summary` を受け取り、assurance warning を `currentStatus` / `nextActions` / `blockers` / `artifacts` へ反映します。
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

### 6. サマリーの読み方

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

### 7. 失敗時の一次切り分け

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

### 8. PR 前チェックリスト

- [ ] `pnpm run verify:lite` が通っている
- [ ] `pnpm run verify:assurance ...` の出力を確認した
- [ ] `artifacts/assurance/assurance-summary.json` が schema-valid である
- [ ] `enforce-assurance` を付ける理由を PR 本文または Issue に記録した
- [ ] strict 運用時に warning / open counterexample を残していない

### 9. 参照

- `docs/quality/assurance-profile.md`
- `docs/quality/assurance-lanes.md`
- `docs/quality/ARTIFACTS-CONTRACT.md`
- `docs/guides/assurance-onboarding-checklist.md`
- `scripts/assurance/aggregate-lanes.mjs`
- `scripts/ci/enforce-assurance-summary.mjs`
- `.github/workflows/verify-lite.yml`
