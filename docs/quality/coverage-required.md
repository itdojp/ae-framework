---
docRole: derived
canonicalSource:
- docs/quality/coverage-policy.md
- policy/quality.json
lastVerified: '2026-03-27'
---
# Coverage Required — Operations Guide for Branch Protection

> Language / 言語: English | 日本語

---

## English

### Purpose
- Keep pull requests report-only by default while making coverage visible to reviewers.
- Enforce coverage on `main` or on explicitly escalated PRs when branch protection requires it.
- Standardize how operators configure repository variables, required checks, and rollout order.

### Recommended Rollout
- Configure repository variables first.
- Observe non-blocking comments before making coverage required.
- Promote the relevant `coverage-check` job status checks, such as `coverage-check / gate` and `coverage-check / coverage`, to required status checks only after thresholds and incident frequency are understood.

### Branch Protection Setup
1. Open Settings -> Variables -> Repository variables.
2. Add:
   - `COVERAGE_ENFORCE_MAIN=1`
   - `COVERAGE_DEFAULT_THRESHOLD` such as `80`
3. Open Settings -> Branches -> Branch protection rules.
4. Enable `Require status checks to pass before merging`.
5. Add the relevant `coverage-check` job status contexts. Depending on the repository state, this may appear as:
   - `coverage-check / gate`
   - `coverage-check / coverage`
6. Optionally relax `Require branches to be up to date before merging` during staged rollout, then enable it again after the policy stabilizes.
7. In staged rollout, keep `verify-lite` required and use `ci-non-blocking` or similar transition controls if the repository is still converging.

### Operational Expectations
- On PRs, comments should display `Coverage (lines):` and `Threshold (effective):`.
- Operators may override the threshold with `/coverage <pct>`.
- Operators may escalate a PR into blocking mode with `/enforce-coverage`.
- On pushes to `main`, `COVERAGE_ENFORCE_MAIN=1` makes coverage enforcement blocking.
- Workflow notes should expose the derivation order `label > repo var > default` and the current policy mode for debugging.

### Display Contract
Coverage comments and notes should make the following fields easy to verify:
- `Threshold (effective)`
- `Derived: label > repo var > default`
- `Policy` / `Policy source`
- links back to this guide and `docs/quality/coverage-policy.md`

### Tips
- Use `/enforce-coverage` when a PR must fail below threshold.
- Use `/coverage <pct>` for a temporary override, for example `72`.
- Clear temporary overrides with `/coverage clear` when that workflow path is available in the current repository state.
- Refer to `docs/quality/coverage-policy.md` for the lower-level policy model and comment semantics.

### Glossary
- `Derived`
  - threshold derivation order: `label > repo var > default`
- `Policy`
  - `enforced` or `report-only`
- `Policy source`
  - `enforced via label: enforce-coverage`
  - `enforced via main + repo vars (COVERAGE_ENFORCE_MAIN)`

### Quick Checklist
- [ ] `COVERAGE_ENFORCE_MAIN` and `COVERAGE_DEFAULT_THRESHOLD` are set
- [ ] the branch protection rule includes the required `coverage-check / gate` and, if used in the rollout, `coverage-check / coverage` context
- [ ] PR comments display `Derived`, `Policy`, and `Policy source`
- [ ] the team has completed an observation period before enforcing coverage broadly

### Notes
- Threshold derivation order is `label > repo var > default (80)`.
- Required enforcement on `main` should be enabled only after the operational baseline is observed and agreed.

## 日本語

### 目的
- PR では既定で report-only としつつ、reviewer に coverage を可視化する
- `main` または明示的に escalate された PR で coverage を強制し、branch protection と整合させる
- repository variable、required check、段階導入の手順を標準化する

### 推奨ロールアウト
- まず repository variable を設定する
- coverage を required にする前に、non-blocking comment の観測期間を設ける
- threshold と incident 頻度を把握した後に、`coverage-check / gate` や `coverage-check / coverage` など必要な job-level status check を required に昇格させる

### Branch protection の設定
1. Settings -> Variables -> Repository variables を開く
2. 次を追加する
   - `COVERAGE_ENFORCE_MAIN=1`
   - `COVERAGE_DEFAULT_THRESHOLD`（例: `80`）
3. Settings -> Branches -> Branch protection rules を開く
4. `Require status checks to pass before merging` を有効化する
5. 対象の `coverage-check` job-level status context を追加する。repository 状態によっては次のいずれかで表示される
   - `coverage-check / gate`
   - `coverage-check / coverage`
6. 段階導入中は `Require branches to be up to date before merging` を一時的に緩め、policy 安定後に再度有効化してよい
7. 段階導入中は `verify-lite` を required のまま維持し、repository が収束するまで `ci-non-blocking` などの移行用制御を使う

### 運用上の期待値
- PR comment には `Coverage (lines):` と `Threshold (effective):` が表示される
- operator は `/coverage <pct>` で threshold を上書きできる
- operator は `/enforce-coverage` で PR を blocking mode に切り替えられる
- `main` への push では `COVERAGE_ENFORCE_MAIN=1` により coverage enforcement が blocking になる
- workflow の Note には `label > repo var > default` の導出順と current policy mode が表示され、debug に使える

### 表示契約
coverage comment と workflow note では、少なくとも次の項目を確認できる状態にする
- `Threshold (effective)`
- `Derived: label > repo var > default`
- `Policy` / `Policy source`
- 本ガイドおよび `docs/quality/coverage-policy.md` への導線

### Tips
- しきい値未満で確実に失敗させたい PR では `/enforce-coverage` を使う
- 一時的な threshold override には `/coverage <pct>` を使う（例: `72`）
- 現在の repository 状態で利用可能なら `/coverage clear` で一時 override を解除する
- policy model と comment semantics の詳細は `docs/quality/coverage-policy.md` を参照する

### 用語集
- `Derived`
  - しきい値導出順: `label > repo var > default`
- `Policy`
  - `enforced` または `report-only`
- `Policy source`
  - `enforced via label: enforce-coverage`
  - `enforced via main + repo vars (COVERAGE_ENFORCE_MAIN)`

### クイックチェックリスト
- [ ] `COVERAGE_ENFORCE_MAIN` と `COVERAGE_DEFAULT_THRESHOLD` が設定されている
- [ ] branch protection rule に required な `coverage-check / gate` と、ロールアウトで使う場合は `coverage-check / coverage` context が追加されている
- [ ] PR comment に `Derived`、`Policy`、`Policy source` が表示される
- [ ] coverage を広く強制する前に観測期間を完了している

### 備考
- しきい値の導出順は `label > repo var > default (80)` である
- `main` の required enforcement は、運用 baseline を観測し合意した後に有効化する
