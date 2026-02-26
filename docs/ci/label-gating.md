# CI Label Gating Policy

> 🌍 Language / 言語: English | 日本語

---

## 日本語（概要）

PR ラベルでゲートを段階的に強化するための方針です（既定は非ブロッキング）。
- `risk:low`, `risk:high`
- `enforce-artifacts`, `enforce-testing`, `enforce-coverage`, `enforce-context-pack`, `coverage:<pct>`, `trace:<id>`, `pr-summary:detailed`
- `run-ci-extended`, `run-integration`, `run-property`, `run-mbt`, `run-mutation`
- オプトイン系: `run-security`（Security/SBOM）、`run-hermetic`（Hermetic CI）、`run-qa`（QA bench）
- 各ワークフローがラベルを読み取り、`continue-on-error` 等を切り替え
- required checks は `verify-lite` + `policy-gate` を想定（`policy/risk-policy.yml` が一次情報）

CI Extended を再実行する際は `.cache/test-results` に保存された成果物が自動復元されます。必要に応じて `node scripts/pipelines/sync-test-results.mjs --status` / `--restore` を実行し、完了後は `--store` で更新してください。差分概要は `node scripts/pipelines/compare-test-trends.mjs` で確認でき、Step Summary にトレンド比較が追記されます。スケジュール実行では `ci-heavy-${ runner.os }-schedule` キーを使って直近 Nightly の baseline を共有し、`heavy-test-trends-history` アーティファクトに履歴を蓄積します。

詳細な動作は以下の英語セクションの Workflows/Automation を参照してください。

Purpose
- Enable gradual tightening of CI by toggling gates per PR using labels. Default remains non‑blocking to avoid disruption.

Labels
- `risk:low`: eligible for auto-merge after required checks pass
- `risk:high`: requires human approval + policy labels + gate
- `enforce-artifacts`: make artifacts validation (ajv) blocking
- `enforce-testing`: make testing scripts (property/replay/BDD lint) blocking
- `enforce-context-pack`: make Context Pack dependency boundary check + E2E validator blocking (`context-pack-quality-gate.yml`)
- `trace:<id>`: set TRACE_ID for focused runs in property/replay scripts
- `pr-summary:detailed`: render a more detailed PR summary (vs. digest)
- `run-ci-extended`: launch the heavy CI Extended workflow (integration, property, MBT, pact, mutation auto diff)
- `run-integration`: run only the integration + pact portion of CI Extended
- `run-property`: run only the property harness portion of CI Extended
- `run-mbt`: run only the MBT smoke (`test:mbt:ci`) portion of CI Extended
- `run-mutation`: run only the mutation auto diff step of CI Extended
- Opt-in (heavy/conditional)
  - `run-security`: trigger Security/SBOM on PRs when deps/crypto/security code change or before release (otherwise weekly cron covers baseline)
  - `run-hermetic`: run Hermetic CI on PRs to validate determinism/network isolation when needed
  - `run-qa`: run QA bench on PRs when behavior/perf regressions are suspected (cron/main covers normal cases)

The CI Extended workflow restores cached heavy test artifacts from `.cache/test-results`. To reuse MBT/property/mutation outputs when re-running locally or via dispatch, run `node scripts/pipelines/sync-test-results.mjs --restore` beforehand (and `--store` afterwards to refresh the cache). Scheduled runs share the `ci-heavy-${ runner.os }-schedule` cache key so that Nightly executions inherit the previous baseline and publish `heavy-test-trends-history` artifacts.

Workflows
- policy-gate.yml: runs `risk-labeler` + `policy-gate`; enforces low/high risk policy, approval, required labels, and label-gated check results
- validate-artifacts-ajv.yml: reads `enforce-artifacts` and passes strict mode to `pnpm run artifacts:validate`
- testing-ddd-scripts.yml: reads `enforce-testing` and makes property/replay/BDD lint blocking only in strict mode; reads `trace:<id>` to focus runs
- context-pack-quality-gate.yml: reads `enforce-context-pack`; runs `context-pack:deps` + `context-pack:e2e-fixture` in report-only/blocking mode
- pr-ci-status-comment.yml: reads `pr-summary:detailed` to switch summary mode; also generates `artifacts/ci/harness-health.{json,md}` and appends Harness Health section to PR summary

Harness Health recommendation
- `artifacts/ci/harness-health.json` emits `recommendedLabels` based on gate states.
- Operators can apply suggested labels (`enforce-artifacts`, `enforce-testing`, `enforce-context-pack`, `run-ci-extended`) to tighten reruns only where needed.

Artifacts
- `pnpm run artifacts:validate` always writes:
  - `artifacts/schema-validation/summary.json`
  - `artifacts/schema-validation/summary.md`
  - `artifacts/schema-validation/errors.json`
- `enforce-artifacts` が付与されると strict モード（スキーマ違反で exit 1）になります。

Testing reproducibility artifacts
- `artifacts/properties/summary.json`
- `artifacts/domain/replay.summary.json`
- `artifacts/mbt/summary.json`
- `artifacts/testing/repro-summary.{json,md}` (CI Step Summary source)

Notes
- These controls are per‑PR. Organization/branch‑wide enforcement can be added later (e.g., always blocking on main) once agreed.

## Automation
- pr-ci-status-comment workflow (label job): adds `trace:<id>` from PR title, sets `pr-summary:detailed` when [detailed] is present.
- `enforce-coverage`: make coverage threshold blocking (default 80%)
- `coverage:<pct>`: set coverage threshold in percent (e.g., coverage:85)
