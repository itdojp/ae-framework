# CI Label Gating Policy

> 🌍 Language / 言語: English | 日本語

---

## 日本語（概要）

PR ラベルでゲートを段階的に強化するための方針です（既定は非ブロッキング）。
- `enforce-artifacts`, `enforce-testing`, `enforce-coverage`, `coverage:<pct>`, `trace:<id>`, `pr-summary:detailed`
- 各ワークフローがラベルを読み取り、`continue-on-error` 等を切り替え

詳細な動作は以下の英語セクションの Workflows/Automation を参照してください。

Purpose
- Enable gradual tightening of CI by toggling gates per PR using labels. Default remains non‑blocking to avoid disruption.

Labels
- `enforce-artifacts`: make artifacts validation (ajv) blocking
- `enforce-testing`: make testing scripts (property/replay/BDD lint) blocking
- `trace:<id>`: set TRACE_ID for focused runs in property/replay scripts
- `pr-summary:detailed`: render a more detailed PR summary (vs. digest)

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
