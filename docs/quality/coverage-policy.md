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
 - Status visibility: Verify Lite のログに既定しきい値/現在の閾値（ラベル/変数）を注記として表示（workflow側でNote出力）。

Step-by-step (enable on main)
1) Settings → Variables → Repository variables に以下を追加します。
   - `COVERAGE_ENFORCE_MAIN=1`
   - `COVERAGE_DEFAULT_THRESHOLD`（例: 80）
2) 必須化は段階導入を推奨します（まずはコメントでの報告→のちにRequired化）。
3) PR では `/coverage <pct>` で個別しきい値、`/enforce-coverage` でブロッキングを選択できます。

Notes
- 変数が未設定でもPRコメントは出力されます（report-only）。
 - Required化の前に main の運用で値と逸脱時の頻度を観測し、適切な閾値を合意してください。

References
- Workflow: `.github/workflows/coverage-check.yml`
- Slash commands: see `AGENTS.md` and `docs/ci-policy.md`

### FAQ
- Q: PRで失敗するのはなぜ？（main以外）
  - A: 既定は report-only です。`/enforce-coverage` ラベルや main への push（+変数設定）以外では失敗しません。失敗している場合はスクリプトの continue-on-error 条件やしきい値導出の設定を確認してください。
- Q: しきい値はどのように決まる？
  - A: `coverage:<pct>` ラベル > リポジトリ変数 `COVERAGE_DEFAULT_THRESHOLD` > 既定 `80` の優先順で決まります。
- Q: main を Required にするには？
  - A: まず `COVERAGE_ENFORCE_MAIN=1` と `COVERAGE_DEFAULT_THRESHOLD` を設定し、十分な観測期間後に Branch protection の Required checks に `coverage-check` を追加してください。

### PR comment example
```
<!-- AE-COVERAGE-SUMMARY -->
Coverage (lines): 82%
Threshold (effective): 80%
- via label: coverage:80
- default: 80%
Policy: report-only
Policy source: report-only
```

### Branch protection（Required化）
1) Settings → Variables → Repository variables に以下を設定
   - `COVERAGE_ENFORCE_MAIN=1`
   - `COVERAGE_DEFAULT_THRESHOLD`（例: 80）
2) Settings → Branches → Branch protection rules → main → Require status checks で
   - `coverage-check / gate` や `coverage-check / coverage` を必要に設定（運用に応じて）
3) 必須化前に一定期間、Note/PRコメントのみで観測することを推奨
