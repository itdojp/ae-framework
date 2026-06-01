---
docRole: ssot
lastVerified: '2026-06-01'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---
# Branch Protection Operations (One-person + AI friendly)

> Language / 言語: English | 日本語

---

## English

Last updated: 2026-06-01

Purpose: manage `main` branch protection through reusable JSON presets without blocking a one-person plus AI workflow, while still keeping deterministic required checks.

### 1. Purpose

- remove the operational dependency on `At least 1 approving review is required` when the repository is intentionally run by one human plus automation
- keep quality control through lightweight required checks even when review counts are relaxed
- separate branch-rule mechanics from approval policy, so `policy-gate` can enforce topology-sensitive approval expectations

### 2. Prerequisites

- create a fine-grained branch-protection admin token with `Repository permissions -> Administration -> Read and write`
  - setup guide: `docs/ci/admin-token-setup.md`
  - usage boundary: the Actions workflow must receive it only as the `branch-protection-admin` environment secret `BRANCH_PROTECTION_ADMIN_TOKEN`; the local fallback may receive it as the local `ADMIN_TOKEN` environment variable
  - prefer a narrowly scoped GitHub App or fine-grained token over a classic admin PAT where repository operations allow it
- configure the protected environment `branch-protection-admin` with required reviewers before enabling the workflow path
  - this environment is the approval boundary for any ADMIN_TOKEN-backed branch-protection mutation
  - do not dispatch emergency presets until the environment approval records the break-glass reason
- confirm the repository side is allowed to use auto-merge if the selected preset assumes merge automation

### 3. Presets under `.github/`

- `branch-protection.main.restore.json`
  - default restore preset
  - requires one approving review and restores the historical `PR Verify / verify` requirement
- `branch-protection.main.relax.json`
  - partial relaxation while keeping one human review
  - emergency / break-glass preset; select `emergency_approval=approved-break-glass` in the workflow only after protected-environment approval
- `branch-protection.main.relax2.json`
  - removes branch-rule review requirements entirely (`required_pull_request_reviews: null`)
  - emergency / break-glass preset; select `emergency_approval=approved-break-glass` in the workflow only after protected-environment approval
- `branch-protection.main.require-verify-lite-gate.json`
  - non-relaxing workflow default
  - requires `verify-lite`, `policy-gate`, and `gate`, while still keeping one approving review
- `branch-protection.main.require-verify-lite.json`
  - older two-check preset requiring `verify-lite` and `policy-gate`, while still keeping one approving review
  - treated as emergency / break-glass by the workflow because it omits the current `gate` check
- `branch-protection.main.verify-lite-noreview.json`
  - preset for intentionally disabling GitHub-native PR review protection
  - requires `verify-lite`, `policy-gate`, and `gate`
  - sets `required_pull_request_reviews` to `null`, disabling GitHub-native review protection and letting `policy-gate` enforce risk, approval, and label-gate conditions
  - uses check contexts (`verify-lite`, `policy-gate`, `gate`), not workflow display names
  - treated as emergency / break-glass by the workflow because it removes native review protection
- `branch-protection.main.verify-lite-trace-noreview.json`
  - trace-required variant for the `#2394` rollout line
  - adds `KvOnce Trace Validation` on top of `verify-lite`, `policy-gate`, and `gate`
  - apply only after the Go / No-Go criteria in `docs/ci/trace-required-criteria.md` are satisfied
  - treated as emergency / break-glass by the workflow because it removes native review protection

### 4. Recorded baseline (`main`, 2026-03-24)

Last recorded `gh api repos/itdojp/ae-framework/branches/main/protection` result:

- `required_status_checks.strict`: `true`
- required contexts: `verify-lite`, `gate`, `policy-gate`
- `required_pull_request_reviews.required_approving_review_count`: `0`
- `required_pull_request_reviews`: enabled, operated with count `0`
- this differs from `branch-protection.main.verify-lite-noreview.json`, which sets `required_pull_request_reviews: null`
- that recorded `main` baseline kept GitHub-native review protection enabled while using `0` required approvals

Repository variables last recorded on 2026-03-24:

- `AE_REVIEW_TOPOLOGY=solo`
- `AE_POLICY_MIN_HUMAN_APPROVALS` is unset
- approval expectations therefore come from `policy-gate` topology rules, not from the branch rule itself

### 5. Applying a preset

#### 5.1 Recommended path: GitHub Actions manual dispatch

1. configure and require approval for the protected environment `branch-protection-admin`
2. register the workflow token as an **environment secret**, not as a repository-wide secret
   - `Settings -> Environments -> branch-protection-admin -> Environment secrets`
   - name: `BRANCH_PROTECTION_ADMIN_TOKEN`
   - value: fine-grained token with Administration read/write
3. remove or avoid repository-wide `ADMIN_TOKEN` for this workflow so an unprotected environment cannot access it
4. open `Actions -> Admin — Apply Branch Protection Preset`
5. run the workflow with choice-based inputs:
   - `branch=main` (the only allowed branch)
   - use the non-relaxing default `preset=branch-protection.main.require-verify-lite-gate.json` for normal changes
   - for emergency presets that remove review or check gates, select `emergency_approval=approved-break-glass` only after the protected-environment approval records the break-glass reason
6. confirm the logs show both the previous and updated values for:
   - `required_pull_request_reviews`
   - `required_status_checks`

Verification command:

```bash
gh api repos/itdojp/ae-framework/branches/main/protection \
  --jq '{strict:.required_status_checks.strict,contexts:.required_status_checks.contexts,reviewCount:(.required_pull_request_reviews.required_approving_review_count // 0)}'
```

#### 5.2 Local application: Node script

```bash
cd ae-framework
ADMIN_TOKEN=ghp_xxx REPO=itdojp/ae-framework BRANCH=main \
  node scripts/admin/apply-branch-protection.mjs .github/branch-protection.main.verify-lite-noreview.json
```

Use the local script when Actions dispatch is unavailable or when an operator needs an explicit, auditable manual fallback.

### 6. Operating policy

- keep `verify-lite`, `policy-gate`, and `gate` as the required branch-protection baseline
- keep `branch-protection.main.require-verify-lite-gate.json` as the workflow default so a manual dispatch does not default to a relaxing preset
- use `branch-protection-admin` environment approval, the environment-scoped `BRANCH_PROTECTION_ADMIN_TOKEN`, and `emergency_approval=approved-break-glass` for any preset that removes review or status-check gates
- do not require `PR Verify / verify` when the repository is operated on the `verify-lite` baseline
- allow auto-merge only when the required checks above are green
- keep heavier enforcement opt-in through labels such as `enforce-coverage` and `enforce-typecov`
- use `AE_REVIEW_TOPOLOGY` to match the operating model
  - `team`: enables human-approval expectations for high-risk PRs
  - `solo`: treats approval count as `0` while keeping the same required checks
- use `AE_POLICY_MIN_HUMAN_APPROVALS` only when an explicit override is needed; it overrides topology-based approval expectations
- these variables assume the topology-aware `policy-gate` implementation is already deployed

### 7. Rollout checklist

- [ ] `Allow auto-merge` is enabled in repository settings
- [ ] `main` required checks are exactly `verify-lite`, `policy-gate`, and `gate`
- [ ] strict up-to-date enforcement is enabled
- [ ] branch-rule review requirements are configured to be compatible with topology-based approval enforcement (choose one)
  - [ ] native PR review protection is disabled: `required_pull_request_reviews=null`
  - [ ] native PR review protection remains enabled with zero required approvals: `required_pull_request_reviews.required_approving_review_count=0`
- [ ] `AE_REVIEW_TOPOLOGY` matches the operating model (`solo` or `team`)
- [ ] `AE_POLICY_MIN_HUMAN_APPROVALS` is set only when an explicit override is needed
- [ ] the repository has decided how `AE_AUTOMATION_PROFILE` interacts with manual variable overrides

### 8. Incident checklist

- [ ] required check names in branch protection match the actual check contexts emitted by workflows
- [ ] when `gate` fails, confirm AI review presence and unresolved review threads first
- [ ] when `policy-gate` fails, inspect `AE_REVIEW_TOPOLOGY`, labels, and risk-policy conditions
- [ ] when auto-merge does not fire, inspect both `Allow auto-merge` and `AE_AUTO_MERGE*`
- [ ] when 429 occurs repeatedly, tune `AE_GH_THROTTLE_MS` and `AE_GH_RETRY_*` conservatively
- [ ] if needed, stop automation with `AE_AUTOMATION_GLOBAL_DISABLE=1`, then recover gradually through the runbook

### 9. Automation helpers

- `ci-auto-rerun-failed` retries a failed job only once. Final judgment still comes from the rerun log and the latest SHA state.
- `pr-ci-status-comment` (PR Maintenance) auto-updates behind PR branches. Merge conflicts still require manual resolution.
- auto-approve can be introduced later if the team decides to keep branch-rule review requirements while allowing tightly scoped machine approval. That path still requires a PAT-backed workflow.

### 10. Rollback and emergency handling

- emergency merge path (not recommended)
  - obtain `branch-protection-admin` environment approval with a recorded break-glass reason
  - temporarily apply `branch-protection.main.relax2.json` with `emergency_approval=approved-break-glass`
  - merge the urgent PR
  - immediately restore the approved baseline preset
- full rollback to the original policy
  - apply `branch-protection.main.restore.json`
- trace-required rollback
  - if `KvOnce Trace Validation` becomes unstable, return to `branch-protection.main.verify-lite-noreview.json` until the rollout criteria are satisfied again

### 11. Quick checklist

- [ ] `BRANCH_PROTECTION_ADMIN_TOKEN` is registered as a `branch-protection-admin` environment secret (`docs/ci/admin-token-setup.md`)
- [ ] `verify-lite` is included in required checks
- [ ] `policy-gate` is included in required checks
- [ ] `gate` is included in required checks for the current operating baseline
- [ ] `KvOnce Trace Validation` is required only after the trace-required rollout is approved
- [ ] `PR Verify / verify` is not included in required checks when the repository runs on the `verify-lite` baseline
- [ ] no unexpected required checks remain on `main`

### 12. Troubleshooting `Expected — Waiting for status to be reported`

If GitHub keeps showing `Expected — Waiting for status to be reported`:

- confirm the required check names configured in branch protection exactly match the emitted check contexts
- confirm the target workflow really runs in PR context and is not skipped by path, label, or event conditions
- remove obsolete required checks from the preset and reapply branch protection
- if stale expectations are attached to an auto-update merge commit, retrigger the PR event with a new push so the latest head SHA emits the current required checks

## 日本語

最終更新: 2026-06-01

目的: `main` ブランチの保護設定を JSON preset で切り替え、1人 + AI の運用で詰まらず、それでも deterministic な Required checks を維持できるようにする。

### 1. 目的

- `At least 1 approving review is required` に依存せず、1人 + AI のワークフローでも停滞しないようにする
- review count を緩和しても、軽量な Required checks で品質を担保する
- branch rule の機械設定と approval policy を分離し、`policy-gate` 側で topology に応じた承認条件を評価できるようにする

### 2. 事前準備

- Fine-grained な branch-protection admin token（`Repository permissions -> Administration -> Read and write`）を作成する
  - 手順: `docs/ci/admin-token-setup.md`
  - 用途: Actions workflow では `branch-protection-admin` environment secret `BRANCH_PROTECTION_ADMIN_TOKEN` としてのみ渡す。ローカル fallback ではローカル環境変数 `ADMIN_TOKEN` として渡してよい
  - repository 運用上可能な場合は classic admin PAT よりも scoped な GitHub App または fine-grained token を優先する
- workflow 経路を有効化する前に、required reviewer 付きの protected environment `branch-protection-admin` を設定する
  - この environment が ADMIN_TOKEN で branch protection を変更する際の approval boundary になる
  - emergency preset は environment approval に break-glass 理由を残してから dispatch する
- 選択した preset が auto-merge 前提の場合は、repository 設定で `Allow auto-merge` が有効であることを確認する

### 3. プリセット一覧（`.github/` 配下）

- `branch-protection.main.restore.json`
  - 復元用の既定 preset
  - review 1 件必須と historical な `PR Verify / verify` を戻す
- `branch-protection.main.relax.json`
  - review 1 件を維持したまま条件を軽く緩和する preset
  - emergency / break-glass preset。protected environment 承認後に workflow で `emergency_approval=approved-break-glass` を選択する
- `branch-protection.main.relax2.json`
  - branch rule 上の review 要件を完全に外す preset（`required_pull_request_reviews: null`）
  - emergency / break-glass preset。protected environment 承認後に workflow で `emergency_approval=approved-break-glass` を選択する
- `branch-protection.main.require-verify-lite-gate.json`
  - relaxing ではない workflow 既定 preset
  - `verify-lite` / `policy-gate` / `gate` を Required にしつつ、review 1 件を維持する
- `branch-protection.main.require-verify-lite.json`
  - `verify-lite` と `policy-gate` を Required にしつつ、review 1 件を維持する旧 two-check preset
  - 現行の `gate` check を含まないため workflow では emergency / break-glass として扱う
- `branch-protection.main.verify-lite-noreview.json`
  - GitHub native の PR review protection を意図的に外す preset
  - `verify-lite` / `policy-gate` / `gate` を Required にする
  - `required_pull_request_reviews` を `null` にし、risk / approval / label-gate は `policy-gate` 側で強制する
  - branch protection に登録するのは workflow 表示名ではなく check context（`verify-lite`, `policy-gate`, `gate`）
  - native review protection を外すため workflow では emergency / break-glass として扱う
- `branch-protection.main.verify-lite-trace-noreview.json`
  - `#2394` 系の trace required 化 preset
  - `verify-lite` / `policy-gate` / `gate` に加えて `KvOnce Trace Validation` を Required にする
  - 適用前に `docs/ci/trace-required-criteria.md` の Go / No-Go 基準を満たすこと
  - native review protection を外すため workflow では emergency / break-glass として扱う

### 4. 記録済みベースライン（`main`, 2026-03-24 時点）

記録済みの `gh api repos/itdojp/ae-framework/branches/main/protection` 確認結果:

- `required_status_checks.strict`: `true`
- required contexts: `verify-lite`, `gate`, `policy-gate`
- `required_pull_request_reviews.required_approving_review_count`: `0`
- `required_pull_request_reviews`: 有効だが count `0` で運用
- これは `branch-protection.main.verify-lite-noreview.json` の `required_pull_request_reviews: null` とは異なる
- その記録時点の `main` baseline は、required approvals を `0` にしつつ GitHub native の review protection 自体は有効のまま維持していた

Repository Variables の確認結果（2026-03-24 時点）:

- `AE_REVIEW_TOPOLOGY=solo`
- `AE_POLICY_MIN_HUMAN_APPROVALS` は未設定
- 承認条件は branch rule ではなく `policy-gate` の topology 評価で管理する

### 5. プリセット適用方法

#### 5.1 推奨: GitHub Actions の手動ディスパッチ

1. protected environment `branch-protection-admin` を設定し、承認必須にする
2. workflow 用 token は repository-wide secret ではなく **environment secret** として登録する
   - `Settings -> Environments -> branch-protection-admin -> Environment secrets`
   - 名前: `BRANCH_PROTECTION_ADMIN_TOKEN`
   - 値: Administration read/write の fine-grained token
3. unprotected environment から参照されないよう、この workflow 用の repository-wide `ADMIN_TOKEN` は削除または使用しない
4. `Actions -> Admin — Apply Branch Protection Preset` を開く
5. choice-based input で workflow を実行する
   - `branch=main`（唯一の許可 branch）
   - 通常変更では relaxing でない既定値 `preset=branch-protection.main.require-verify-lite-gate.json` を使う
   - review/check gate を外す emergency preset は、protected environment 承認で break-glass 理由を残した後に限り `emergency_approval=approved-break-glass` を選ぶ
6. 実行ログで、更新前後の次の値を確認する
   - `required_pull_request_reviews`
   - `required_status_checks`

確認コマンド:

```bash
gh api repos/itdojp/ae-framework/branches/main/protection \
  --jq '{strict:.required_status_checks.strict,contexts:.required_status_checks.contexts,reviewCount:(.required_pull_request_reviews.required_approving_review_count // 0)}'
```

#### 5.2 ローカル適用: Node script

```bash
cd ae-framework
ADMIN_TOKEN=ghp_xxx REPO=itdojp/ae-framework BRANCH=main \
  node scripts/admin/apply-branch-protection.mjs .github/branch-protection.main.verify-lite-noreview.json
```

Actions dispatch が使えない場合や、明示的な manual fallback を監査可能な形で残したい場合に使う。

### 6. 運用指針

- branch protection の Required checks は `verify-lite` / `policy-gate` / `gate` を baseline とする
- workflow の既定 preset は `branch-protection.main.require-verify-lite-gate.json` に保ち、手動 dispatch が relaxing preset から始まらないようにする
- review/check gate を外す preset には `branch-protection-admin` environment approval、environment-scoped `BRANCH_PROTECTION_ADMIN_TOKEN`、`emergency_approval=approved-break-glass` の両方を要求する
- `verify-lite` baseline では `PR Verify / verify` を Required に含めない
- auto-merge は上記 Required checks が green のときだけ許可する
- 重い enforcement は `enforce-coverage`、`enforce-typecov` などの label で opt-in に保つ
- `AE_REVIEW_TOPOLOGY` で運用体制を表現する
  - `team`: high-risk PR に人手承認要件を有効化する
  - `solo`: approval count を `0` として評価し、Required checks は維持する
- `AE_POLICY_MIN_HUMAN_APPROVALS` は明示 override が必要な場合だけ使う。設定した場合は topology より優先する
- 上記変数は topology-aware な `policy-gate` 実装が導入済みであることが前提

### 7. 導入時チェックリスト

- [ ] `Allow auto-merge` が有効
- [ ] `main` の Required checks が `verify-lite`, `policy-gate`, `gate` の3つ
- [ ] strict（up-to-date 要件）が有効
- [ ] branch rule の review 要件が topology-based approval enforcement と整合している
  - [ ] native PR review protection を無効化: `required_pull_request_reviews=null`
  - [ ] native PR review protection を有効のまま required approvals だけ `0` にする: `required_pull_request_reviews.required_approving_review_count=0`
- [ ] `AE_REVIEW_TOPOLOGY` が体制に応じて設定済み（`solo` または `team`）
- [ ] `AE_POLICY_MIN_HUMAN_APPROVALS` は必要時のみ設定
- [ ] `AE_AUTOMATION_PROFILE` と個別変数 override の関係を決定済み

### 8. 障害時チェックリスト

- [ ] branch protection の required contexts と workflow が出す check context が一致している
- [ ] `gate` fail の場合、AI review 未投稿と unresolved thread を優先確認する
- [ ] `policy-gate` fail の場合、`AE_REVIEW_TOPOLOGY`、labels、risk policy を確認する
- [ ] auto-merge 未発火時、`Allow auto-merge` と `AE_AUTO_MERGE*` を確認する
- [ ] 429 が連続する場合、`AE_GH_THROTTLE_MS` と `AE_GH_RETRY_*` を保守的に調整する
- [ ] 必要なら `AE_AUTOMATION_GLOBAL_DISABLE=1` で停止し、runbook に沿って段階復旧する

### 9. 運用補助（自動化）

- `ci-auto-rerun-failed` は失敗 job を **1回だけ** 自動再実行する。最終判断は rerun log と最新 SHA 状態で行う
- `pr-ci-status-comment`（PR Maintenance）は behind PR branch を自動更新する。merge conflict は手動解決が必要
- branch rule の review 要件を残しつつ機械承認を導入したい場合は、後から auto-approve workflow を追加できる。ただし PAT を使う workflow が前提

### 10. ロールバックと緊急対応

- 緊急で PR を通したい場合（推奨しない）
  - `branch-protection-admin` environment 承認で break-glass 理由を記録する
  - `emergency_approval=approved-break-glass` 付きで一時的に `branch-protection.main.relax2.json` を適用する
  - 対象 PR を merge する
  - 直後に承認済み baseline preset へ戻す
- 元の状態へ完全復元する場合
  - `branch-protection.main.restore.json` を適用する
- trace required 化の巻き戻し
  - `KvOnce Trace Validation` が不安定な場合は、Go / No-Go 基準を満たすまで `branch-protection.main.verify-lite-noreview.json` へ戻す

### 11. クイックチェックリスト

- [ ] `BRANCH_PROTECTION_ADMIN_TOKEN` を `branch-protection-admin` environment secret として登録済み（`docs/ci/admin-token-setup.md`）
- [ ] `verify-lite` が Required に含まれている
- [ ] `policy-gate` が Required に含まれている
- [ ] 現行 baseline で `gate` が Required に含まれている
- [ ] `KvOnce Trace Validation` は trace required rollout 承認後だけ Required になっている
- [ ] `verify-lite` baseline では `PR Verify / verify` が Required に含まれていない
- [ ] `main` に想定外の Required checks が残っていない

### 12. `Expected — Waiting for status to be reported` の対処

GitHub で `Expected — Waiting for status to be reported` が出続ける場合は、次を確認する。

- branch protection に登録した Required check 名が、実際に出力される check context と完全一致しているか
- 対象 workflow が PR 文脈で本当に実行される設定になっているか（path / label / event 条件で skip されていないか）
- 不要になった Required check は preset から削除し、branch protection を再適用する
- auto-update merge commit に stale な期待値が残っている場合は、新しい push で PR event を再発火し、最新 head SHA から current required checks を出し直す
