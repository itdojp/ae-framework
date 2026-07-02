---
docRole: derived
canonicalSource:
- docs/quality/coverage-policy.md
- policy/quality.json
lastVerified: '2026-07-02'
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
- Promote the relevant `coverage-check` job status checks, such as `coverage-check / gate` and `coverage-check / coverage`, to required status checks only after the current ratchet threshold and incident frequency are understood.
- Keep the long-term target at `80%`, but raise the enforced `main` threshold through `configs/coverage-ratchet.json.mainThreshold` in reviewable increments.

### Branch Protection Setup
1. Open Settings -> Variables -> Repository variables.
2. Add:
   - `COVERAGE_ENFORCE_MAIN=1`
   - optional `COVERAGE_TARGET_THRESHOLD` such as `80` when the target differs from the checked-in default
3. Confirm that `configs/coverage-ratchet.json.mainThreshold` matches the latest observed `main` baseline.
4. Open Settings -> Branches -> Branch protection rules.
5. Enable `Require status checks to pass before merging`.
6. Add the relevant `coverage-check` job status contexts. Depending on the repository state, this may appear as:
   - `coverage-check / gate`
   - `coverage-check / coverage`
7. Optionally relax `Require branches to be up to date before merging` during staged rollout, then enable it again after the policy stabilizes.
8. In staged rollout, keep `verify-lite` required and use `ci-non-blocking` or similar transition controls if the repository is still converging.

### Operational Expectations
- On PRs, comments should display `Coverage (lines):` and `Threshold (effective):`.
- Operators may override the threshold with `/coverage <pct>`.
- Operators may escalate a PR into blocking mode with `/enforce-coverage`.
- On pushes to `main`, `COVERAGE_ENFORCE_MAIN=1` makes coverage enforcement blocking at the current ratchet threshold.
- Workflow notes should expose the derivation order `label > main ratchet > repo var > default` and the current policy mode for debugging.

### Display Contract
Coverage comments and notes should make the following fields easy to verify:
- `Threshold (effective)`
- `Derived: label > main ratchet > repo var > default` in workflow notes; PR comments may display the PR-specific order `label > repo var > default`
- `Policy` / `Policy source`
- `Threshold source`, `Ratchet threshold`, and `Target threshold` for enforced `main` push diagnostics
- links back to this guide and `docs/quality/coverage-policy.md`

### Tips
- Use `/enforce-coverage` when a PR must fail below threshold.
- Use `/coverage <pct>` for a temporary override, for example `72`.
- Clear temporary overrides with `/coverage clear` when that workflow path is available in the current repository state.
- Refer to `docs/quality/coverage-policy.md` for the lower-level policy model and comment semantics.

### Glossary
- `Derived`
  - workflow note threshold derivation order: `label > main ratchet > repo var > default`
- `Policy`
  - `enforced` or `report-only`
- `Policy source`
  - `enforced via label: enforce-coverage`
  - `enforced via main + repo vars (COVERAGE_ENFORCE_MAIN)`

### Quick Checklist
- [ ] `COVERAGE_ENFORCE_MAIN` is set
- [ ] `configs/coverage-ratchet.json.mainThreshold` matches the latest accepted `main` baseline
- [ ] `configs/coverage-ratchet.json.targetThreshold` remains `80` until the project explicitly changes the long-term target
- [ ] the branch protection rule includes the required `coverage-check / gate` and, if used in the rollout, `coverage-check / coverage` context
- [ ] PR comments display `Derived`, `Policy`, and `Policy source`
- [ ] the team has completed an observation period before enforcing coverage broadly

### Notes
- Workflow-note threshold derivation order is `label > main ratchet > repo var > default (80)`.
- Required enforcement on `main` should be enabled only after the operational baseline is observed and agreed; ratchet increases should be small, reviewed PRs.

## 日本語

### 目的
- PR では既定で報告専用（report-only）としつつ、レビュアに coverage を可視化する
- `main` または明示的にエスカレートされた PR で coverage を強制し、branch protection と整合させる
- リポジトリ変数、required checks、段階導入の手順を標準化する

### 推奨ロールアウト
- まずリポジトリ変数を設定する
- coverage を required にする前に、non-blocking な PR comment の観測期間を設ける
- 現行 ratchet threshold と incident 頻度を把握した後に、`coverage-check / gate` や `coverage-check / coverage` など必要な job-level status check を required に昇格させる
- 長期目標は `80%` のまま維持しつつ、`configs/coverage-ratchet.json.mainThreshold` を reviewable な増分で引き上げる

### Branch protection
1. Settings -> Variables -> Repository variables を開く
2. 次を追加する
   - `COVERAGE_ENFORCE_MAIN=1`
   - target を checked-in default から変える場合のみ `COVERAGE_TARGET_THRESHOLD`（例: `80`）
3. `configs/coverage-ratchet.json.mainThreshold` が latest observed `main` baseline と整合していることを確認する
4. Settings -> Branches -> Branch protection rules を開く
5. `Require status checks to pass before merging` を有効化する
6. 対象の `coverage-check` job-level status context を追加する。リポジトリ状態によっては次のいずれかで表示される
   - `coverage-check / gate`
   - `coverage-check / coverage`
7. 段階導入中は `Require branches to be up to date before merging` を一時的に緩め、ポリシー安定後に再度有効化してよい
8. 段階導入中は `verify-lite` を required のまま維持し、リポジトリが収束するまで `ci-non-blocking` などの移行用制御を使う

### 運用上の期待値
- PR comment には `Coverage (lines):` と `Threshold (effective):` が表示される
- 運用担当者は `/coverage <pct>` でしきい値を上書きできる
- 運用担当者は `/enforce-coverage` で PR を blocking mode に切り替えられる
- `main` への push では `COVERAGE_ENFORCE_MAIN=1` により、現行 ratchet threshold で coverage enforcement が blocking になる
- workflow の注記には `label > main ratchet > repo var > default` の導出順と現在のポリシーモードが表示され、デバッグに使える

### 表示契約
coverage comment と workflow note では、少なくとも次の項目を確認できる状態にする
- `Threshold (effective)`
- workflow note の `Derived: label > main ratchet > repo var > default`。PR comment では PR 専用の `label > repo var > default` が表示される場合がある
- `Policy` / `Policy source`
- `main` push 診断用の `Threshold source`、`Ratchet threshold`、`Target threshold`
- 本ガイドおよび `docs/quality/coverage-policy.md` への導線

### Tips
- しきい値未満で確実に失敗させたい PR では `/enforce-coverage` を使う
- 一時的なしきい値 override には `/coverage <pct>` を使う（例: `72`）
- 現在のリポジトリ状態で利用可能なら `/coverage clear` で一時 override を解除する
- ポリシーモデルと comment semantics の詳細は `docs/quality/coverage-policy.md` を参照する

### 用語集
- `Derived`
  - workflow note のしきい値導出順: `label > main ratchet > repo var > default`
- `Policy`
  - `enforced` または `report-only`
- `Policy source`
  - `enforced via label: enforce-coverage`
  - `enforced via main + repo vars (COVERAGE_ENFORCE_MAIN)`

### クイックチェックリスト
- [ ] `COVERAGE_ENFORCE_MAIN` が設定されている
- [ ] `configs/coverage-ratchet.json.mainThreshold` が latest accepted `main` baseline と一致している
- [ ] project が長期目標を明示的に変更するまでは `configs/coverage-ratchet.json.targetThreshold` が `80` のままである
- [ ] branch protection に required な `coverage-check / gate` と、ロールアウトで使う場合は `coverage-check / coverage` context が追加されている
- [ ] PR comment に `Derived`、`Policy`、`Policy source` が表示される
- [ ] coverage を広く強制する前に観測期間を完了している

### 備考
- workflow note のしきい値導出順は `label > main ratchet > repo var > default (80)` である
- `main` の required enforcement は、運用 baseline を観測し合意した後に有効化する。ratchet の引き上げは小さく、レビュー済み PR として行う
