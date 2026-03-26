---
docRole: derived
canonicalSource:
- policy/quality.json
- docs/quality/verification-gates.md
lastVerified: '2026-03-27'
---
# Coverage Policy — Proposal and Operations

> Language / 言語: English | 日本語

---

## English

### Goals
- Keep PR handling fast and report-only by default.
- Escalate to blocking coverage checks only when operators or branch policy explicitly request it.
- Allow the `main` branch to enforce thresholds through repository variables without changing every PR workflow.

### Mechanics

Threshold source order:
1. PR label `coverage:<pct>` such as `coverage:75`
2. Repository variable `COVERAGE_DEFAULT_THRESHOLD` with default `80`

Label parsing rules:
- the last matching label wins
- accepted range is `0` to `100`
- `%` and surrounding spaces are trimmed
- the `coverage:` prefix is case-insensitive

Blocking enforcement is enabled when:
- the PR has the `enforce-coverage` label, or
- the workflow runs on a push to `main` and repository variable `COVERAGE_ENFORCE_MAIN=1`

Reporting behavior:
- `.github/workflows/coverage-check.yml` posts a non-blocking PR comment that records effective coverage, threshold source, and current policy state
- Verify Lite logs also note the default threshold and the effective threshold derived from labels or repository variables

### Recommended Operations
- On PRs, use `/coverage <pct>` for ad-hoc threshold overrides.
- On PRs, use `/enforce-coverage` when coverage should become blocking.
- On `main`, configure repository variables `COVERAGE_ENFORCE_MAIN=1` and `COVERAGE_DEFAULT_THRESHOLD=<pct>`.
- Roll out branch protection in stages: start with report-only comments, then make `coverage-check` required after the threshold is stable.

### Step-by-Step: Enable on `main`
1. In Settings -> Variables -> Repository variables, add:
   - `COVERAGE_ENFORCE_MAIN=1`
   - `COVERAGE_DEFAULT_THRESHOLD` such as `80`
2. Observe comment-only output first and confirm that the threshold is realistic for current `main`.
3. After the operational baseline is stable, add the relevant `coverage-check` status contexts to branch protection.

### Notes
- PR comments are still emitted when the repository variables are unset; this remains report-only behavior.
- Agree on the threshold only after observing real deviation frequency on `main`.
- Coverage policy affects coverage gating only. It does not replace broader `verify-lite`, `policy-gate`, or `gate` requirements.

### Development (Local Verify)
- Dry-run the summary composer locally without posting to GitHub:

```bash
AE_COVERAGE_DRY_RUN=1 \
GITHUB_TOKEN=dummy \
GITHUB_REPOSITORY=owner/repo \
GITHUB_EVENT_NAME=pull_request \
GITHUB_EVENT_PATH=event.json \
node scripts/coverage/pr-coverage-summary.mjs
```

- The script searches for coverage JSON in this order:
  - `coverage/coverage-summary.json`
  - `artifacts/coverage/coverage-summary.json`
- The default project command emits the required JSON summary:

```bash
pnpm run coverage
```

- Override the summary path with `AE_COVERAGE_SUMMARY_PATH` when an alternate file already exists.
- Disable comment posting for CI experiments with `AE_COVERAGE_SKIP_COMMENT=1`.

### FAQ
- Why does a PR fail outside `main`?
  - The default is report-only. Outside `main`, failures usually mean `enforce-coverage` was applied or the workflow logic around threshold derivation was modified.
- How is the threshold chosen?
  - `coverage:<pct>` label -> repository variable `COVERAGE_DEFAULT_THRESHOLD` -> default `80`.
- How do we make `main` required?
  - Set `COVERAGE_ENFORCE_MAIN=1`, set `COVERAGE_DEFAULT_THRESHOLD`, observe for a period, then add the relevant `coverage-check` status context in branch protection.
- Why is `coverage-summary.json` missing under strict execution?
  - Confirm that `pnpm run coverage` emits the `json-summary` reporter output and that CI preserves the generated `coverage/` content.

### PR Comment Example
```text
<!-- AE-COVERAGE-SUMMARY -->
Coverage (lines): 82%
Threshold (effective): 80%
Source: label
- via label: coverage:80
- repo var: COVERAGE_DEFAULT_THRESHOLD=80%
- default: 80%
Derived: label > repo var > default
Rules: label override last-wins; accepts 0–100; trims %/spaces
Policy: report-only
Policy source: report-only
Docs: docs/quality/coverage-required.md
Docs: docs/quality/coverage-policy.md
Docs: docs/ci/label-gating.md
Reproduce: coverage -> coverage/coverage-summary.json -> total.lines.pct
Reproduce: threshold -> label coverage:<pct> > vars.COVERAGE_DEFAULT_THRESHOLD > default 80
Tips: /coverage <pct> to override; /enforce-coverage to enforce
```

### Branch Protection
1. Set repository variables:
   - `COVERAGE_ENFORCE_MAIN=1`
   - `COVERAGE_DEFAULT_THRESHOLD`
2. In Settings -> Branches -> Branch protection rules -> `main` -> Require status checks, add the relevant `coverage-check` contexts such as `coverage-check / gate` or `coverage-check / coverage`.
3. Keep an observation period before making the check strictly required.

### References
- Workflow: `.github/workflows/coverage-check.yml`
- Slash commands: `../../AGENTS.md`, `../ci-policy.md`
- Related docs:
  - `docs/quality/coverage-required.md`
  - `docs/quality/verification-gates.md`
  - `docs/ci/label-gating.md`

## 日本語

### 目的
- PR 処理は既定で高速かつ report-only に保つ
- operator または branch policy が明示した場合のみ coverage を blocking に引き上げる
- `main` では repository variable によって threshold を統制し、各 PR workflow の個別改修を避ける

### 仕組み

しきい値の決定順序:
1. PR label `coverage:<pct>`（例: `coverage:75`）
2. Repository variable `COVERAGE_DEFAULT_THRESHOLD`（既定値 `80`）

label の解釈規則:
- 最後に付与された一致 label を採用
- 受け付ける範囲は `0`〜`100`
- `%` と前後の空白を除去
- `coverage:` prefix は大文字小文字を区別しない

blocking enforcement は次のいずれかで有効になります。
- PR に `enforce-coverage` label が付いている
- `main` への push で workflow が実行され、かつ `COVERAGE_ENFORCE_MAIN=1` が設定されている

reporting の挙動:
- `.github/workflows/coverage-check.yml` は non-blocking な PR comment を投稿し、effective coverage、threshold source、現在の policy state を記録する
- Verify Lite のログにも、既定 threshold と label / variable から導出した effective threshold を注記として出力する

### 推奨運用
- PR では `/coverage <pct>` で一時的なしきい値 override を行う
- PR では `/enforce-coverage` で coverage を blocking に切り替える
- `main` では `COVERAGE_ENFORCE_MAIN=1` と `COVERAGE_DEFAULT_THRESHOLD=<pct>` を repository variable に設定する
- branch protection は段階導入とし、まずは report-only comment で観測し、その後 `coverage-check` を required にする

### `main` で有効化する手順
1. Settings -> Variables -> Repository variables に次を追加する
   - `COVERAGE_ENFORCE_MAIN=1`
   - `COVERAGE_DEFAULT_THRESHOLD`（例: `80`）
2. まず comment-only の観測期間を設け、現在の `main` に対して threshold が現実的かを確認する
3. 運用 baseline が安定したら、branch protection に関連する `coverage-check` status context を追加する

### 注意事項
- repository variable が未設定でも PR comment は出力される。これは report-only 挙動である
- threshold は `main` での逸脱頻度を実測したうえで合意する
- coverage policy は coverage gate だけを制御する。`verify-lite`、`policy-gate`、`gate` 全体の代替ではない

### Development（ローカル検証）
- GitHub 投稿なしで summary composer を dry-run する:

```bash
AE_COVERAGE_DRY_RUN=1 \
GITHUB_TOKEN=dummy \
GITHUB_REPOSITORY=owner/repo \
GITHUB_EVENT_NAME=pull_request \
GITHUB_EVENT_PATH=event.json \
node scripts/coverage/pr-coverage-summary.mjs
```

- script は coverage JSON を次の順で探索する
  - `coverage/coverage-summary.json`
  - `artifacts/coverage/coverage-summary.json`
- 既定の project command は必要な JSON summary を出力する:

```bash
pnpm run coverage
```

- 別の summary file を使う場合は、既存 file を `AE_COVERAGE_SUMMARY_PATH` で明示する
- CI 実験で comment 投稿を止める場合は `AE_COVERAGE_SKIP_COMMENT=1` を使う

### FAQ
- `main` 以外の PR で failure になるのはなぜか
  - 既定は report-only。`enforce-coverage` が付いたか、threshold 導出ロジックが変更された可能性を確認する
- しきい値はどう決まるか
  - `coverage:<pct>` label -> repository variable `COVERAGE_DEFAULT_THRESHOLD` -> 既定 `80`
- `main` を required にするにはどうするか
  - `COVERAGE_ENFORCE_MAIN=1` と `COVERAGE_DEFAULT_THRESHOLD` を設定し、一定期間観測した後に branch protection へ追加する
- strict 実行で `coverage-summary.json` が missing になるのはなぜか
  - `pnpm run coverage` が `json-summary` reporter を出力しているか、および CI が `coverage/` の生成物を保持しているかを確認する

### PR comment 例
```text
<!-- AE-COVERAGE-SUMMARY -->
Coverage (lines): 82%
Threshold (effective): 80%
Source: label
- via label: coverage:80
- repo var: COVERAGE_DEFAULT_THRESHOLD=80%
- default: 80%
Derived: label > repo var > default
Rules: label override last-wins; accepts 0–100; trims %/spaces
Policy: report-only
Policy source: report-only
Docs: docs/quality/coverage-required.md
Docs: docs/quality/coverage-policy.md
Docs: docs/ci/label-gating.md
Reproduce: coverage -> coverage/coverage-summary.json -> total.lines.pct
Reproduce: threshold -> label coverage:<pct> > vars.COVERAGE_DEFAULT_THRESHOLD > default 80
Tips: /coverage <pct> to override; /enforce-coverage to enforce
```

### Branch protection
1. repository variable を設定する
   - `COVERAGE_ENFORCE_MAIN=1`
   - `COVERAGE_DEFAULT_THRESHOLD`
2. Settings -> Branches -> Branch protection rules -> `main` -> Require status checks で、`coverage-check / gate` や `coverage-check / coverage` など必要な context を追加する
3. strict に required 化する前に、一定期間は観測期間を設ける

### 参照
- Workflow: `.github/workflows/coverage-check.yml`
- Slash commands: `../../AGENTS.md`, `../ci-policy.md`
- 関連文書:
  - `docs/quality/coverage-required.md`
  - `docs/quality/verification-gates.md`
  - `docs/ci/label-gating.md`
