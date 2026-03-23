---
docRole: ssot
lastVerified: '2026-03-24'
owner: docs-governance
verificationCommand: pnpm -s run check:doc-consistency
---
# CI Operations Handbook

最終更新: 2026-03-06

目的: 日次運用で使う確認手順・再実行手順・停止判断を 1 ページで参照できるようにする。

責務境界:
- 方針（Required checks / opt-in）は `docs/ci-policy.md` を正とする
- 本書は「運用手順（運転方法）」のみを扱い、詳細診断は runbook へ委譲する
- 境界表は `docs/ci/ci-doc-boundary-matrix.md` を参照

## English

Last updated: 2026-03-24

Purpose: provide a single daily-operations page for CI checks, reruns, and stop/recovery decisions.

Scope boundary:
- `docs/ci-policy.md` remains the source of truth for required checks and opt-in controls
- this handbook only documents operator procedures; deep diagnosis stays in dedicated runbooks
- use `docs/ci/ci-doc-boundary-matrix.md` when the scope boundary is unclear

### 1. Daily operations

1. Check failing open PRs
   `gh pr list --state open`
2. Extract failed / pending jobs
   `gh pr checks <PR_NUMBER>`
3. Narrow the view to required checks
   `gh pr checks <PR_NUMBER> --required`

### 2. Standard failure-response flow

1. Pull the failed job log
   `gh run view <RUN_ID> --log-failed`
2. Classify the failure
   - configuration / permission (`label`, token, workflow permissions)
   - lockfile mismatch (`ERR_PNPM_LOCKFILE_CONFIG_MISMATCH`, `pnpm install --frozen-lockfile`)
   - implementation drift (workflow / script / docs mismatch)
   - transient failure (429, network, runner)
3. Re-evaluate against the correct SHA
   - if a new commit was pushed, inspect the new run created by that push
   - if the same SHA should be retried, use `gh run rerun <RUN_ID> --failed`

### 3. Representative operating cases

#### 3.1 Copilot Review Gate fails
- confirm unresolved thread count and keep replying / resolving until it reaches `0`
- if only a stale fail remains, rerun the failed gate run

#### 3.2 Docs Doctest fails
- first distinguish `doctest-index` from `doctest-full`
- local replay:
  - index: `DOCTEST_ENFORCE=1 pnpm run test:doctest:index`
  - changed markdown: `DOCTEST_ENFORCE=1 pnpm run test:doctest:pr-changed -- --base-ref origin/main`
  - full: `DOCTEST_ENFORCE=1 pnpm run test:doctest:full`
- docs-doctest policy drift check:
  - `node scripts/ci/check-docs-doctest-policy-sync.mjs`
- governance-only PRs still need preflight because adding front matter expands the changed-markdown doctest surface
- documentation snippets and pseudo payloads should use `text` or `no-doctest` fences instead of runnable `bash` / `typescript` / `javascript` fences unless execution is intended

#### 3.3 `pnpm install --frozen-lockfile` fails
- classify the lane using `docs/ci-policy.md`
  - jobs shown in `gh pr checks <PR_NUMBER> --required` are `required-lane`
  - `workflow_dispatch`-only flows are `manual-ops`
  - explicit non-required PR lanes are `optional-pr`
- for `required-lane`, refresh `pnpm-lock.yaml` with `pnpm install`, then commit and push the lockfile change
- after the lockfile fix, inspect the new run created for the latest head branch
  - `gh run list --branch <HEAD_BRANCH> --limit 20`
- use `gh run rerun <RUN_ID> --failed` only when no new push-based run will be created

#### 3.4 429 / secondary rate limit
- avoid repeated dispatch bursts for the same change
- prefer `rerun --failed` before manual redispatch
- raise `AE_GH_THROTTLE_MS` when needed (default: `250ms`)

#### 3.5 `enforce-assurance` fails
- confirm `artifacts/assurance/assurance-summary.json` exists
- inspect `warningCount`, `warningClaims`, `claimsMissingRequiredLanes`, `claimsMissingRequiredEvidenceKinds`, and `unlinkedCounterexamples`
- verify `claimCount` is not `0`
- inspect each claim's `missingLanes`, `missingEvidenceKinds`, and `counterexamples.open`
- use `docs/quality/assurance-operations-runbook.md` as the primary runbook

### 4. Fail-safe stop and recovery

#### 4.1 Emergency stop
- `AE_AUTOMATION_GLOBAL_DISABLE=1`

#### 4.2 Partial stop
- `AE_CODEX_AUTOPILOT_ENABLED=0`
- `AE_SELF_HEAL_ENABLED=0`
- `AE_COPILOT_AUTO_FIX=0`

#### 4.3 Recovery
1. fix the root cause
2. restore the stop variables
3. resume the target workflows gradually via `workflow_dispatch`

### 5. Record template for issue / PR comments

- occurrence time (UTC)
- failing workflow / job
- log source `runId`
- remediation applied
- rerun result
- recurrence prevention, if needed

### 6. Related docs

- `docs/ci/ci-doc-boundary-matrix.md`
- `docs/ci-policy.md`
- `docs/ci/ci-troubleshooting-guide.md`
- `docs/ci/pr-automation.md`
- `docs/ci/copilot-review-gate.md`
- `docs/ci/docs-doctest-policy.md`
- `docs/ci/automation-failure-policies.md`
- `docs/quality/assurance-operations-runbook.md`

## 1. 日次オペレーション（開始時）

1. Open PR の失敗チェックを確認する  
   `gh pr list --state open`
2. 失敗/保留ジョブを抽出する  
   `gh pr checks <PR番号>`
3. Required checks のみ確認する  
   `gh pr checks <PR番号> --required`

## 2. 失敗時の標準対応フロー

1. 失敗ジョブのログを取得する  
   `gh run view <runId> --log-failed`
2. 原因を分類する
   - 設定/権限（label・token・permissions）
   - lockfile 不整合（`ERR_PNPM_LOCKFILE_CONFIG_MISMATCH` / `pnpm install --frozen-lockfile` fail）
   - 実装不整合（workflow/script/doc drift）
   - 一時障害（429、network、runner）
3. 修正後、対象 SHA を確認して再評価する  
   - 新しい commit を push した場合は、その push で生成された run を確認する
   - 同一 SHA の失敗ジョブだけを再試行したい場合は `gh run rerun <runId> --failed`

## 3. 代表的な運用ケース

### 3.1 Copilot Review Gate が失敗

- 未解決 thread 数を確認し、未解決が 0 になるまで返信/resolve する
- stale fail が残る場合は fail 側 run を rerun する

### 3.2 Docs Doctest が失敗

- まず `doctest-index` か `doctest-full` かを判別する
- ローカル再現
  - index: `DOCTEST_ENFORCE=1 pnpm run test:doctest:index`
  - changed-markdown: `DOCTEST_ENFORCE=1 pnpm run test:doctest:pr-changed -- --base-ref origin/main`
  - full: `DOCTEST_ENFORCE=1 pnpm run test:doctest:full`
- docs-doctest 設定ドリフト検査
  - `node scripts/ci/check-docs-doctest-policy-sync.mjs`
- front matter 追加だけでも changed-markdown doctest 対象が増えるため、governance 拡張 PR では preflight を必須とする
- 説明用 snippet / 出力例 / 擬似 payload は `text` または `no-doctest` 付き fence を使い、実行可能な `bash` / `typescript` / `javascript` fence を安易に追加しない

### 3.3 `pnpm install --frozen-lockfile` が失敗

- lane 判定は `docs/ci-policy.md` の Lockfile reproducibility を source of truth とし、`gh pr checks <PR番号> --required` に出る job は `required-lane`、`workflow_dispatch` 専用は `manual-ops`、それ以外で明示的に非必須化されたものだけを `optional-pr` と扱う
- `required-lane` は `pnpm install` で `pnpm-lock.yaml` を更新し、差分を commit / push する
- PR の lockfile 修正後は新しい `pull_request` run が自動生成されるため、その最新 run を確認する
  - `gh run list --branch <head-branch> --limit 20`
- `gh run rerun <runId> --failed` は push 後に新 run が作られない手動系 workflow や、最新 SHA に対する failed run の再試行時だけ使う
- `optional-pr` / `manual-ops` は例外 lane（`optional-pr`: 明示的に非必須化された PR lane、`manual-ops`: 手動オペレーション専用 lane）。fallback 実装があっても標準対応は同じく lockfile 更新を優先する

### 3.4 429 / secondary rate limit

- 同一変更を短時間で連続 dispatch しない
- 先に `rerun --failed` を使う
- 必要に応じて `AE_GH_THROTTLE_MS` を引き上げる（既定 250ms）

### 3.5 `enforce-assurance` が失敗

- `artifacts/assurance/assurance-summary.json` が生成されているか確認する
- `warningCount` / `warningClaims` / `claimsMissingRequiredLanes` / `claimsMissingRequiredEvidenceKinds` / `unlinkedCounterexamples` を確認する
- `claimCount` が `0` になっていないか確認する
- claim ごとの `missingLanes` / `missingEvidenceKinds` / `counterexamples.open` を見て不足証跡を補う
- 一次情報は `docs/quality/assurance-operations-runbook.md` を参照する

## 4. 停止・復帰（Fail-safe）

### 4.1 自動化停止（緊急）

- `AE_AUTOMATION_GLOBAL_DISABLE=1`

### 4.2 部分停止

- `AE_CODEX_AUTOPILOT_ENABLED=0`
- `AE_SELF_HEAL_ENABLED=0`
- `AE_COPILOT_AUTO_FIX=0`

### 4.3 復帰

1. 根本原因の修正
2. 停止変数を戻す
3. 対象 workflow を dispatch で段階再開

## 5. 記録テンプレート（Issue/PRコメント）

- 発生時刻（UTC）
- 失敗 workflow/job
- 取得ログ runId
- 実施した修正
- rerun 結果
- 再発防止（必要時）

## 6. 関連ドキュメント

- `docs/ci/ci-doc-boundary-matrix.md`
- `docs/ci-policy.md`
- `docs/ci/ci-troubleshooting-guide.md`
- `docs/ci/pr-automation.md`
- `docs/ci/copilot-review-gate.md`
- `docs/ci/docs-doctest-policy.md`
- `docs/ci/automation-failure-policies.md`
- `docs/quality/assurance-operations-runbook.md`
