---
docRole: ssot
lastVerified: '2026-03-26'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---
# CI Label Gating Policy

> 🌍 Language / 言語: English | 日本語

---

## English

### Purpose

Use PR labels to tighten CI gates incrementally. The default posture remains report-only so routine PRs are not blocked unnecessarily.

- Primary current-state required checks on `main`: `verify-lite`, `policy-gate`, and `gate`
- Risk and enforcement labels let operators raise only the checks needed for the current PR
- The authoritative sources for required-gate behavior are `policy/risk-policy.yml` and the active branch-protection preset

### Labels

- `risk:low`: eligible for auto-merge after required checks pass
- `risk:high`: requires human approval, policy labels, and required-gate convergence
- `enforce-artifacts`: make AJV-based artifact validation blocking
- `enforce-testing`: make property / replay / BDD lint scripts blocking
- `enforce-coverage`: make coverage threshold enforcement blocking
- `enforce-context-pack`: make Context Pack dependency-boundary checks and the E2E validator blocking
- `enforce-discovery`: make strict Discovery Pack validation blocking in `verify-lite.yml`
- `coverage:<pct>`: set coverage threshold in percent, for example `coverage:85`
- `trace:<id>`: set focused trace scope for property / replay / related scripts
- `pr-summary:detailed`: render the detailed PR summary mode instead of the digest mode
- `run-ci-extended`: run the heavy CI Extended lane
- `run-integration`: run only the integration and pact portion of CI Extended
- `run-property`: run only the property-harness portion of CI Extended
- `run-mbt`: run only the MBT smoke portion of CI Extended
- `run-mutation`: run only the mutation auto-diff portion of CI Extended
- `run-trace`: require trace gate checks on the PR context
- Heavy / conditional opt-ins:
  - `run-security`: Security / SBOM workflows when dependency or security-sensitive changes justify it
  - `run-hermetic`: Hermetic CI for determinism or network-isolation checks
  - `run-qa`: QA bench when behavioral or performance regressions are suspected

### CI Extended cache and trend reuse

The CI Extended lane restores heavy test artifacts from `.cache/test-results`.

- Run `node scripts/pipelines/sync-test-results.mjs --status` to inspect cache state
- Run `node scripts/pipelines/sync-test-results.mjs --restore` before local reruns or manual dispatch when you want the previous heavy baseline
- Run `node scripts/pipelines/sync-test-results.mjs --store` after a successful rerun to refresh the cache
- Run `node scripts/pipelines/compare-test-trends.mjs` to inspect trend deltas written into the Step Summary
- Scheduled runs share the `ci-heavy-${ runner.os }-schedule` cache key and publish `heavy-test-trends-history`

### Workflows

- `policy-gate.yml`
  - runs `risk-labeler` and `policy-gate`
  - emits `policy-input.v1` and JS decision artifacts
  - executes OPA shadow compare against `policy/risk-policy.rego`
- `validate-artifacts-ajv.yml`
  - is called by `spec-validation.yml` with a `strict` input
  - `strict: true` is set when the `enforce-artifacts` label is present on the PR
  - in strict mode, generates trace / verify-lite artifacts before running `pnpm run artifacts:validate`
- `testing-ddd-scripts.yml`
  - reads `enforce-testing`
  - makes property / replay / BDD lint blocking only in strict mode
  - reads `trace:<id>` for focused runs
- `context-pack-quality-gate.yml`
  - reads `enforce-context-pack`
  - runs `context-pack:deps` and `context-pack:e2e-fixture` in report-only or blocking mode
- `verify-lite.yml`
  - reads `enforce-discovery`
  - keeps Discovery Pack validate report-only by default
  - enables strict fail-on and `plan-spec` compile dry-run only when the label is present
- `spec-generate-model.yml`
  - publishes `KvOnce Trace Validation` on non-fork PRs
  - always emits `trace-conformance`
  - becomes policy-blocking when `run-trace` is required on high-risk PRs
- `pr-ci-status-comment.yml`
  - reads `pr-summary:detailed`
  - generates `artifacts/ci/harness-health.{json,md}`
  - appends Harness Health to the PR summary

### `run-trace` convergence steps

If `policy-gate` fails because trace checks are missing:

1. Wait until `Spec Generate & Model Tests` (`.github/workflows/spec-generate-model.yml`) completes on the same PR context
2. Confirm either `trace-conformance` or `KvOnce Trace Validation` is `success`
3. Wait for `policy-gate` to re-evaluate automatically; if it does not, dispatch `policy-gate` manually with the same PR number

### Harness Health recommendation

- `artifacts/ci/harness-health.json` emits `recommendedLabels`
- Operators can apply suggested labels such as `enforce-artifacts`, `enforce-testing`, `enforce-context-pack`, `run-trace`, `run-ci-extended`, and `autopilot:on`
- `run-conformance` is legacy compatibility wording; use `run-trace` as the canonical label

### Artifacts

Policy and artifact-validation outputs include:

- `artifacts/ci/policy-input-v1.json`
- `artifacts/ci/policy-decision-js-v1.json`
- `artifacts/ci/policy-decision-opa-v1.json`
- `artifacts/ci/policy-shadow-compare-v1.json`
- `artifacts/schema-validation/summary.json`
- `artifacts/schema-validation/summary.md`
- `artifacts/schema-validation/errors.json`

When `enforce-artifacts` is present, strict mode also generates prerequisite trace and verify-lite outputs before validation:

- `artifacts/hermetic-reports/trace/kvonce-events.ndjson`
- `artifacts/hermetic-reports/trace/kvonce-projection.json`
- `artifacts/hermetic-reports/trace/kvonce-validation.json`
- `artifacts/hermetic-reports/trace/projected/kvonce-state-sequence.json`
- `artifacts/verify-lite/verify-lite-run-summary.json`
- `artifacts/report-envelope.json`
- `artifacts/trace/report-envelope.json`

Without the label, the workflow stays lightweight and runs only `artifacts:validate`.

### Testing reproducibility artifacts

- `artifacts/properties/summary.json`
- `artifacts/domain/replay.summary.json`
- `artifacts/mbt/summary.json`
- `artifacts/testing/repro-summary.{json,md}`

### Automation

- `pr-ci-status-comment` can add `trace:<id>` from the PR title
- `[detailed]` in the PR title enables `pr-summary:detailed`
- `enforce-coverage` makes the coverage threshold blocking
- `coverage:<pct>` overrides the default coverage threshold

### Notes

These controls are PR-scoped. Organization-wide or branch-wide mandatory enforcement can be layered later after operational agreement.

## 日本語

### 目的

PR ラベルで CI ゲートを段階的に強化するための方針です。既定値は report-only を維持し、通常 PR を過剰にブロックしない運用を前提とします。

- current-state の `main` Required checks は `verify-lite` / `policy-gate` / `gate`
- リスク系ラベルと強制系ラベルで、その PR に必要なゲートだけを引き上げる
- required-gate の一次情報は `policy/risk-policy.yml` と有効な branch protection preset

### ラベル

- `risk:low`: Required checks 通過後に auto-merge 対象になれる
- `risk:high`: human approval、policy labels、required gate の収束を要求する
- `enforce-artifacts`: AJV ベースの artifact validation を blocking にする
- `enforce-testing`: property / replay / BDD lint を blocking にする
- `enforce-coverage`: coverage threshold を blocking にする
- `enforce-context-pack`: Context Pack dependency boundary と E2E validator を blocking にする
- `enforce-discovery`: `verify-lite.yml` 内の Discovery Pack strict validation を blocking にする
- `coverage:<pct>`: coverage threshold を上書きする。例: `coverage:85`
- `trace:<id>`: property / replay などの focused trace scope を指定する
- `pr-summary:detailed`: digest ではなく detailed PR summary を描画する
- `run-ci-extended`: heavy な CI Extended lane を起動する
- `run-integration`: CI Extended の integration / pact 部分のみを起動する
- `run-property`: CI Extended の property harness 部分のみを起動する
- `run-mbt`: CI Extended の MBT smoke 部分のみを起動する
- `run-mutation`: CI Extended の mutation auto-diff 部分のみを起動する
- `run-trace`: PR 文脈で trace gate checks を required 扱いにする
- heavy / conditional opt-in:
  - `run-security`: dependency 変更や security-sensitive 変更時の Security / SBOM
  - `run-hermetic`: determinism / network isolation 確認のための Hermetic CI
  - `run-qa`: 振る舞い・性能劣化が疑われるときの QA bench

### CI Extended の cache / trend 再利用

CI Extended lane は `.cache/test-results` に保存された heavy test artifacts を復元できます。

- cache 状態確認: `node scripts/pipelines/sync-test-results.mjs --status`
- local rerun / manual dispatch 前の復元: `node scripts/pipelines/sync-test-results.mjs --restore`
- successful rerun 後の更新: `node scripts/pipelines/sync-test-results.mjs --store`
- trend 差分確認: `node scripts/pipelines/compare-test-trends.mjs`
- scheduled run は `ci-heavy-${ runner.os }-schedule` を共有し、`heavy-test-trends-history` を publish する

### Workflows

- `policy-gate.yml`
  - `risk-labeler` と `policy-gate` を実行する
  - `policy-input.v1` と JS decision artifacts を出力する
  - `policy/risk-policy.rego` に対する OPA shadow compare を実行する
- `validate-artifacts-ajv.yml`
  - `spec-validation.yml` から `strict` input 付きで呼ばれる
  - PR に `enforce-artifacts` があると `strict: true` が渡される
  - strict では trace / verify-lite artifacts を先に生成してから `pnpm run artifacts:validate` を実行する
- `testing-ddd-scripts.yml`
  - `enforce-testing` を読む
  - property / replay / BDD lint を strict のときだけ blocking にする
  - `trace:<id>` で focused run を行う
- `context-pack-quality-gate.yml`
  - `enforce-context-pack` を読む
  - `context-pack:deps` と `context-pack:e2e-fixture` を report-only / blocking で切り替える
- `verify-lite.yml`
  - `enforce-discovery` を読む
  - 既定では Discovery Pack validate を report-only に保つ
  - ラベルがあるときだけ strict fail-on と `plan-spec` compile dry-run を有効化する
- `spec-generate-model.yml`
  - non-fork PR では `KvOnce Trace Validation` を publish する
  - 常に `trace-conformance` を出力する
  - high-risk PR で `run-trace` が required の場合、policy 側で blocking 扱いになる
- `pr-ci-status-comment.yml`
  - `pr-summary:detailed` を読む
  - `artifacts/ci/harness-health.{json,md}` を生成する
  - PR summary に Harness Health を追記する

### `run-trace` の収束手順

`policy-gate` が trace check 未充足で失敗した場合は、次の順で収束させます。

1. `Spec Generate & Model Tests`（`.github/workflows/spec-generate-model.yml`）が同じ PR 文脈で完了するまで待つ
2. `trace-conformance` または `KvOnce Trace Validation` が `success` であることを確認する
3. `policy-gate` の自動再評価を待つ。自動で動かなければ同じ PR 番号で `policy-gate` を手動 dispatch する

### Harness Health の推奨ラベル

- `artifacts/ci/harness-health.json` は `recommendedLabels` を出力する
- `enforce-artifacts`、`enforce-testing`、`enforce-context-pack`、`run-trace`、`run-ci-extended`、`autopilot:on` などを必要箇所だけ再適用できる
- `run-conformance` は legacy compatibility wording であり、canonical label は `run-trace`

### 成果物

policy / artifact validation 系の主な出力:

- `artifacts/ci/policy-input-v1.json`
- `artifacts/ci/policy-decision-js-v1.json`
- `artifacts/ci/policy-decision-opa-v1.json`
- `artifacts/ci/policy-shadow-compare-v1.json`
- `artifacts/schema-validation/summary.json`
- `artifacts/schema-validation/summary.md`
- `artifacts/schema-validation/errors.json`

`enforce-artifacts` が付与された strict mode では、検証前に次の trace / verify-lite outputs も生成します。

- `artifacts/hermetic-reports/trace/kvonce-events.ndjson`
- `artifacts/hermetic-reports/trace/kvonce-projection.json`
- `artifacts/hermetic-reports/trace/kvonce-validation.json`
- `artifacts/hermetic-reports/trace/projected/kvonce-state-sequence.json`
- `artifacts/verify-lite/verify-lite-run-summary.json`
- `artifacts/report-envelope.json`
- `artifacts/trace/report-envelope.json`

ラベル未付与時は軽量運用として `artifacts:validate` のみを実行します。

### テスト再現成果物

- `artifacts/properties/summary.json`
- `artifacts/domain/replay.summary.json`
- `artifacts/mbt/summary.json`
- `artifacts/testing/repro-summary.{json,md}`

### Automation

- `pr-ci-status-comment` は PR title から `trace:<id>` を付与できる
- PR title に `[detailed]` があると `pr-summary:detailed` を有効化する
- `enforce-coverage` は coverage threshold を blocking にする
- `coverage:<pct>` は default threshold を上書きする

### 補足

これらの controls は PR 単位です。organization-wide / branch-wide の強制運用は、合意後に追加します。
