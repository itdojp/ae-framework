# Coverage Policy — Proposal and Operations

Goals
- Keep PRs fast and non-blocking by default; gate only on explicit signals
- Allow main branch to enforce thresholds via repository variables

Mechanics
- Threshold source order:
  1. PR label `coverage:<pct>` (e.g., `coverage:75`)
  2. Repository variable `COVERAGE_DEFAULT_THRESHOLD` (default 80)
- Enforcement (blocking) when:
  - PR has label `enforce-coverage`, or
  - Push to `main` and repository variable `COVERAGE_ENFORCE_MAIN` = `1`
- Reporting:
  - The `coverage-check` workflow posts a non-blocking PR comment with computed coverage and policy state

Recommended operations
- On PRs: use `/coverage <pct>` for ad-hoc thresholds and `/enforce-coverage` when you want blocking
- On `main`: set `COVERAGE_ENFORCE_MAIN=1` and `COVERAGE_DEFAULT_THRESHOLD` in repository variables

Step-by-step (enable on main)
1) Settings → Variables → Repository variables に以下を追加します。
   - `COVERAGE_ENFORCE_MAIN=1`
   - `COVERAGE_DEFAULT_THRESHOLD`（例: 80）
2) 必須化は段階導入を推奨します（まずはコメントでの報告→のちにRequired化）。
3) PR では `/coverage <pct>` で個別しきい値、`/enforce-coverage` でブロッキングを選択できます。

Notes
- 変数が未設定でもPRコメントは出力されます（report-only）。

References
- Workflow: `.github/workflows/coverage-check.yml`
- Slash commands: see `AGENTS.md` and `docs/ci-policy.md`
