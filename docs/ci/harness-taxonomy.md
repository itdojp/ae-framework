# Harness Failure Taxonomy

## 目的

複数のCIゲート（artifacts schema / testing harness / context-pack / CI Extended）を横断し、失敗を同一フォーマットで要約して次アクションを出す。

- 出力: `artifacts/ci/harness-health.json`, `artifacts/ci/harness-health.md`
- 生成ポイント:
  - PR: `.github/workflows/pr-ci-status-comment.yml` の `summarize` job
  - 週次: `.github/workflows/ci-extended.yml` の schedule 実行

## JSON契約（`harness-health/v1`）

主要フィールド:

- `commitSha`, `workflow`, `runId`
- `gates.{artifactsSchema|testingHarness|contextPack|ciExtended}.status` (`ok|warn|fail|skip`)
- `severity` (`ok|warn|critical`)
- `reasons[]`
- `recommendedLabels[]`
- `reproducibleHints[]` (`gate`, `trace`, `seed`, `command`)

## Taxonomy定義

`harness-health` は以下カテゴリをゲート判定から導出する。

| Category | 判定起点 | 典型ラベル | 主な再現入口 |
| --- | --- | --- | --- |
| `CONTRACT_SCHEMA` | `artifactsSchema=fail/warn` | `enforce-artifacts` | `pnpm run artifacts:validate -- --strict=true` |
| `DETERMINISTIC_TEST_FAIL` | `testingHarness=fail` | `enforce-testing` | `gh workflow run testing-ddd-scripts.yml --repo <owner/repo>` |
| `FLAKE_SUSPECTED` | `testingHarness=warn`（pending/inconclusive） | `enforce-testing` | `trace:<id>` + `test:replay:focus` |
| `BOUNDARY_VIOLATION` | `contextPack=fail/warn` | `enforce-context-pack` | `pnpm run context-pack:deps` |
| `PERF_REGRESSION` | `ciExtended=fail/warn`（heavy trend summary） | `run-ci-extended` | `gh workflow run ci-extended.yml` |
| `INFRA` | チェック取得不可やCI都合で判定不能 | `needs-investigation`（運用側） | workflow run logs |

補足:
- `severity=critical` は、いずれかのゲートが `fail` の場合に設定。
- `severity=warn` は、`fail` が無く `warn` が1件以上ある場合に設定。

## 運用

### PR運用（`pr-ci-status-comment`）

- PRコメントに `Harness Health` セクションを追記する。
- `pr-summary:detailed` の場合、`Reasons` と `Reproducible Hints` を詳細表示する。
- `recommendedLabels` は次回実行の強化ラベル候補として使う。

### 週次運用（`ci-extended` schedule）

- schedule実行時に `harness-health` を生成し、artifactとして保存する。
- `severity=critical` の場合は `ci-stability` / `needs-investigation` ラベルでIssueを起票する。
- 同一タイトルのopen Issueがある場合は重複起票しない。

## 担当の入口

- CI担当: `severity` と `recommendedLabels` を見てゲート再実行方針を決める。
- 実装担当: `reasons` と `reproducibleHints.command` でローカル再現する。
- 監視担当: 週次Issueの増減で不安定化トレンドを確認する。
