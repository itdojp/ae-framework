---
docRole: ssot
lastVerified: '2026-03-26'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---
# Harness Failure Taxonomy

> Language / 言語: English | 日本語

---

## English

Summarize failures from multiple CI gates (artifacts schema / testing harness / context-pack / runtime conformance / CI Extended / UI E2E) in one contract so operators can choose the next action consistently.

- Outputs: `artifacts/ci/harness-health.json`, `artifacts/ci/harness-health.md`
- Schema: `schema/harness-health.schema.json`
- Validation:
  - `scripts/ci/validate-artifacts-ajv.mjs`
  - `scripts/ci/validate-json.mjs`
- Emission points:
  - PR: `summarize` job in `.github/workflows/pr-ci-status-comment.yml`
  - Weekly: scheduled run of `.github/workflows/ci-extended.yml`

### JSON contract (`harness-health/v1`)

Primary fields:

- `commitSha`, `workflow`, `runId`
- `contractId` (`harness-health.v1`)
- `gates.{artifactsSchema|testingHarness|contextPack|runtimeConformance|ciExtended|uiE2E}.status` (`ok|warn|fail|skip`)
- `severity` (`ok|warn|critical`)
- `reasons[]`
- `recommendedLabels[]`
- `recommendedContextChanges[]` (`file`, `changeType`, `targetId`, `rationale`, `suggestedCommand`)
- `reproducibleHints[]` (`gate`, `trace`, `seed`, `command`)

### Taxonomy

`harness-health` derives the following categories from gate outcomes.

| Category | Detection source | Typical labels | Main reproduction entrypoint |
| --- | --- | --- | --- |
| `CONTRACT_SCHEMA` | `artifactsSchema=fail/warn` | `enforce-artifacts` | `bash scripts/trace/run-kvonce-conformance.sh --input samples/trace/kvonce-sample.ndjson --format ndjson --output-dir artifacts/hermetic-reports/trace && node scripts/ci/write-verify-lite-summary.mjs && node scripts/trace/create-report-envelope.mjs artifacts/verify-lite/verify-lite-run-summary.json artifacts/report-envelope.json && mkdir -p artifacts/trace && cp artifacts/report-envelope.json artifacts/trace/report-envelope.json && pnpm run artifacts:validate -- --strict=true` |
| `DETERMINISTIC_TEST_FAIL` | `testingHarness=fail` | `enforce-testing` | `gh workflow run testing-ddd-scripts.yml --repo <owner/repo>` |
| `FLAKE_SUSPECTED` | `testingHarness=warn` (`pending` / `inconclusive`) | `enforce-testing` | `trace:<id>` + `test:replay:focus` |
| `BOUNDARY_VIOLATION` | `contextPack=fail/warn` | `enforce-context-pack` | `pnpm run context-pack:deps -- --strict=true && pnpm run context-pack:e2e-fixture` |
| `RUNTIME_CONFORMANCE` | `runtimeConformance=fail/warn` | `run-trace` (legacy: `run-conformance`), `autopilot:on` | `gh workflow run runtime-conformance-self-heal.yml --repo <owner/repo> -f trace_input=samples/conformance/sample-traces.json -f apply_fixes=false -f dry_run=true` |
| `PERF_REGRESSION` | `ciExtended=fail/warn` (heavy trend summary) | `run-ci-extended` | `gh workflow run ci-extended.yml --repo <owner/repo>` |
| `UI_SEMANTIC_E2E` | `uiE2E=fail/warn` | `run-e2e` | `pnpm exec playwright install --with-deps chromium && pnpm run ui-e2e:semantic` |
| `INFRA` | check retrieval unavailable or CI environment prevented evaluation | `needs-investigation` (operations side) | workflow run logs |

Notes:
- Set `severity=critical` when any gate is `fail`.
- Set `severity=warn` when there is no `fail` and at least one `warn`.
- In strict `enforce-artifacts` reproduction, generate trace / verify-lite artifacts before running `artifacts:validate`.

### Operations

#### PR operation (`pr-ci-status-comment`)

- Append a `Harness Health` section to the PR comment.
- When `pr-summary:detailed` is set, show `Reasons`, `Reproducible Hints`, and `Context Pack Suggested Changes` in detail.
- Use `recommendedLabels` as candidates for the next stricter rerun.

#### Weekly operation (`ci-extended` schedule)

- Generate `harness-health` during scheduled runs and persist it as an artifact.
- If `severity=critical`, open an issue with labels such as `ci-stability` / `needs-investigation`.
- Do not open a duplicate issue when an issue with the same title is already open.

### Role handoff

- CI operators decide rerun policy from `severity` and `recommendedLabels`.
- Implementers reproduce locally from `reasons` and `reproducibleHints.command`.
- Observability / operations owners watch weekly issue volume to detect instability trends.

## 日本語

複数のCIゲート（artifacts schema / testing harness / context-pack / runtime conformance / CI Extended / UI E2E）を横断し、失敗を同一フォーマットで要約して次アクションを出す。

- 出力: `artifacts/ci/harness-health.json`, `artifacts/ci/harness-health.md`
- Schema: `schema/harness-health.schema.json`
- Validation:
  - `scripts/ci/validate-artifacts-ajv.mjs`
  - `scripts/ci/validate-json.mjs`
- 生成ポイント:
  - PR: `.github/workflows/pr-ci-status-comment.yml` の `summarize` job
  - 週次: `.github/workflows/ci-extended.yml` の schedule 実行

### JSON契約（`harness-health/v1`）

主要フィールド:

- `commitSha`, `workflow`, `runId`
- `contractId` (`harness-health.v1`)
- `gates.{artifactsSchema|testingHarness|contextPack|runtimeConformance|ciExtended|uiE2E}.status` (`ok|warn|fail|skip`)
- `severity` (`ok|warn|critical`)
- `reasons[]`
- `recommendedLabels[]`
- `recommendedContextChanges[]` (`file`, `changeType`, `targetId`, `rationale`, `suggestedCommand`)
- `reproducibleHints[]` (`gate`, `trace`, `seed`, `command`)

### Taxonomy定義

`harness-health` は以下カテゴリをゲート判定から導出する。

| Category | 判定起点 | 典型ラベル | 主な再現入口 |
| --- | --- | --- | --- |
| `CONTRACT_SCHEMA` | `artifactsSchema=fail/warn` | `enforce-artifacts` | `bash scripts/trace/run-kvonce-conformance.sh --input samples/trace/kvonce-sample.ndjson --format ndjson --output-dir artifacts/hermetic-reports/trace && node scripts/ci/write-verify-lite-summary.mjs && node scripts/trace/create-report-envelope.mjs artifacts/verify-lite/verify-lite-run-summary.json artifacts/report-envelope.json && mkdir -p artifacts/trace && cp artifacts/report-envelope.json artifacts/trace/report-envelope.json && pnpm run artifacts:validate -- --strict=true` |
| `DETERMINISTIC_TEST_FAIL` | `testingHarness=fail` | `enforce-testing` | `gh workflow run testing-ddd-scripts.yml --repo <owner/repo>` |
| `FLAKE_SUSPECTED` | `testingHarness=warn`（`pending` / `inconclusive`） | `enforce-testing` | `trace:<id>` + `test:replay:focus` |
| `BOUNDARY_VIOLATION` | `contextPack=fail/warn` | `enforce-context-pack` | `pnpm run context-pack:deps` |
| `RUNTIME_CONFORMANCE` | `runtimeConformance=fail/warn` | `run-trace`（旧表記: `run-conformance`）, `autopilot:on` | `gh workflow run runtime-conformance-self-heal.yml --repo <owner/repo> -f trace_input=samples/conformance/sample-traces.json -f apply_fixes=false -f dry_run=true` |
| `PERF_REGRESSION` | `ciExtended=fail/warn`（heavy trend summary） | `run-ci-extended` | `gh workflow run ci-extended.yml` |
| `UI_SEMANTIC_E2E` | `uiE2E=fail/warn` | `run-e2e` | `pnpm exec playwright install chromium && pnpm run ui-e2e:semantic` |
| `INFRA` | チェック取得不可やCI都合で判定不能 | `needs-investigation`（運用側） | workflow run logs |

補足:
- `severity=critical` は、いずれかのゲートが `fail` の場合に設定。
- `severity=warn` は、`fail` が無く `warn` が1件以上ある場合に設定。
- `enforce-artifacts` の strict 再現では、`artifacts:validate` 実行前に trace/verify-lite artifacts を生成する。

### 運用

#### PR運用（`pr-ci-status-comment`）

- PRコメントに `Harness Health` セクションを追記する。
- `pr-summary:detailed` の場合、`Reasons` / `Reproducible Hints` / `Context Pack Suggested Changes` を詳細表示する。
- `recommendedLabels` は次回実行の強化ラベル候補として使う。

#### 週次運用（`ci-extended` schedule）

- schedule実行時に `harness-health` を生成し、artifactとして保存する。
- `severity=critical` の場合は `ci-stability` / `needs-investigation` ラベルでIssueを起票する。
- 同一タイトルのopen Issueがある場合は重複起票しない。

### 担当の入口

- CI担当: `severity` と `recommendedLabels` を見てゲート再実行方針を決める。
- 実装担当: `reasons` と `reproducibleHints.command` でローカル再現する。
- 監視担当: 週次Issueの増減で不安定化トレンドを確認する。
