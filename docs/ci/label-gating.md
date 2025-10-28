# CI Label Gating Policy

> 🌍 Language / 言語: English | 日本語

---

## 日本語（概要）

PR ラベルでゲートを段階的に強化するための方針です（既定は非ブロッキング）。
- `enforce-artifacts`, `enforce-testing`, `enforce-coverage`, `coverage:<pct>`, `trace:<id>`, `pr-summary:detailed`
- `run-ci-extended`, `run-integration`, `run-property`, `run-mbt`, `run-mutation`
- 各ワークフローがラベルを読み取り、`continue-on-error` 等を切り替え

CI Extended を再実行する際は `.cache/test-results` に保存された成果物が自動復元されます。必要に応じて `node scripts/pipelines/sync-test-results.mjs --status` / `--restore` を実行し、完了後は `--store` で更新してください。差分概要は `node scripts/pipelines/compare-test-trends.mjs` で確認でき、Step Summary にトレンド比較が追記されます。

詳細な動作は以下の英語セクションの Workflows/Automation を参照してください。

Purpose
- Enable gradual tightening of CI by toggling gates per PR using labels. Default remains non‑blocking to avoid disruption.

Labels
- `enforce-artifacts`: make artifacts validation (ajv) blocking
- `enforce-testing`: make testing scripts (property/replay/BDD lint) blocking
- `trace:<id>`: set TRACE_ID for focused runs in property/replay scripts
- `pr-summary:detailed`: render a more detailed PR summary (vs. digest)
- `run-ci-extended`: launch the heavy CI Extended workflow (integration, property, MBT, pact, mutation auto diff)
- `run-integration`: run only the integration + pact portion of CI Extended
- `run-property`: run only the property harness portion of CI Extended
- `run-mbt`: run only the MBT smoke (`test:mbt:ci`) portion of CI Extended
- `run-mutation`: run only the mutation auto diff step of CI Extended

The CI Extended workflow restores cached heavy test artifacts from `.cache/test-results`. To reuse MBT/property/mutation outputs when re-running locally or via dispatch, run `node scripts/pipelines/sync-test-results.mjs --restore` beforehand (and `--store` afterwards to refresh the cache).

Workflows
- validate-artifacts-ajv.yml: reads `enforce-artifacts` and toggles `continue-on-error`
- testing-ddd-scripts.yml: reads `enforce-testing` and toggles `continue-on-error`; reads `trace:<id>` to focus runs
- pr-summary-comment.yml: reads `pr-summary:detailed` to switch summary mode

Notes
- These controls are per‑PR. Organization/branch‑wide enforcement can be added later (e.g., always blocking on main) once agreed.

## Automation
- auto-labels workflow: adds `trace:<id>` from PR title, sets `pr-summary:detailed` when [detailed] is present.
- `enforce-coverage`: make coverage threshold blocking (default 80%)
- `coverage:<pct>`: set coverage threshold in percent (e.g., coverage:85)
