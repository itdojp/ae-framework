---
docRole: ssot
lastVerified: '2026-03-31'
owner: development-docs
verificationCommand: pnpm -s run check:doc-consistency
---

# Agent Collaboration Setup (GitHub-Driven, Zero Manual Handoff)

> 🌍 Language / 言語: English | 日本語

---

## English

### Overview
This document describes how multiple agents such as PM, architecture, and implementation workers can coordinate through GitHub signals only, from planning through implementation, review, merge, and reporting. The assumed baseline is that each agent runs in a separate local workspace on the same machine, typically WSL2 Ubuntu.

Safe local subagent operation is not defined here. Use `docs/agents/multi-agent-safety.md` and `docs/maintenance/subagent-worktree-runbook.md` as the primary references for that topic.

### Prerequisites
- repository administrator access for branch protection and Actions settings
- `gh`, `git`, Node.js, and `pnpm`
- one workspace per agent, for example `~/ws/pm-high`, `~/ws/arch-high`, `~/ws/impl-1`

### 1) GitHub-side setup

#### Labels for role, status, sprint, and epic
Example commands:

```bash
gh label create "role:PM-HIGH" --color C2F5FF || true
gh label create "role:ARCH-HIGH" --color C2F5FF || true
gh label create "role:IMPL-MED-1" --color C2F5FF || true
gh label create "role:IMPL-MED-2" --color C2F5FF || true
gh label create "role:IMPL-MED-3" --color C2F5FF || true

gh label create "status:ready" --color D4F8D4 || true
gh label create "status:in-progress" --color FFE8A3 || true
gh label create "status:review" --color A3D8FF || true
gh label create "status:blocked" --color FFBCBC || true
gh label create "status:done" --color CCCCCC || true

gh label create "sprint:0" --color EAEAEA || true
gh label create "sprint:1" --color EAEAEA || true
gh label create "sprint:2" --color EAEAEA || true
gh label create "sprint:3" --color EAEAEA || true

# Optional epic labels. Referencing an epic in the issue body is also acceptable.
gh label create "epic:#898" --color EAEAEA || true
gh label create "epic:#701" --color EAEAEA || true
gh label create "epic:#786" --color EAEAEA || true
gh label create "epic:#879" --color EAEAEA || true
```

#### Milestones for sprints
```bash
gh api repos/:owner/:repo/milestones -X POST -f title='Sprint 0' -f state='open' || true
gh api repos/:owner/:repo/milestones -X POST -f title='Sprint 1' -f state='open' || true
gh api repos/:owner/:repo/milestones -X POST -f title='Sprint 2' -f state='open' || true
gh api repos/:owner/:repo/milestones -X POST -f title='Sprint 3' -f state='open' || true
```

#### Branch protection on `main`
Configure branch protection under Settings -> Branches -> Branch protection rules.

Recommended baseline:
- require review approval and CODEOWNERS review when applicable
- require current PR lane checks such as `verify-lite`, `policy-gate`, and `gate`
- keep merge policy consistent with repository review topology

#### CODEOWNERS for review routing
Example `.github/CODEOWNERS`:

```text
policy/** @org/arch-team
quality/** @org/arch-team
packages/spec-compiler/** @org/arch-team
docs/** @org/pm-team
```

Current repository note:
- this repository currently routes the default path and the explicit paths above to `@ootakazuhiko`
- if you later switch to team routing, keep `.github/CODEOWNERS` and this document aligned

#### Pull request template
Prepare `.github/pull_request_template.md` with checks for goal, scope, acceptance criteria, impact, risk, rollback, and related issues.

#### Minimum GitHub Actions set
Current minimal workflow set:
- `triage.yml`: normalizes status and role labels on issue events
- `slash-commands.yml`: optional issue-comment command entrypoint. Enable issue-side slash commands only when needed
- `agent-commands.yml`: primary command handler for issue-side automation in the current repository
- `verify-lite.yml`: required lightweight verification lane
- `quality-gates-centralized.yml`: centralized quality gate runner

Current repository note:
- `pr-quality.yml` is not part of the current baseline
- quality and merge gating are handled through `verify-lite.yml` and `quality-gates-centralized.yml`
- future reporting workflows such as progress summary or model evaluation should be documented as additive follow-up, not assumed as already active

> Note: set Actions permissions in Settings -> Actions -> General to "Read and write permissions" when the workflow needs to update labels, comments, or issue/PR metadata.

### 2) Recommended minimum repository layout
- `.github/CODEOWNERS`
- `.github/pull_request_template.md`
- `.github/workflows/triage.yml`
- `.github/workflows/slash-commands.yml`
- `.github/workflows/agent-commands.yml`
- `.github/workflows/verify-lite.yml`
- `.github/workflows/quality-gates-centralized.yml`
- `policy/quality.json` for staged DoD gate rollout from warning to blocking

### 3) Workspace setup for each agent on WSL
Shared setup example:

```bash
mkdir -p ~/ws/{pm-high,arch-high,impl-1,impl-2,impl-3}
cd ~/ws/impl-1 && gh repo clone itdojp/ae-framework
git config user.name "agent-impl-1"
git config user.email "agent-impl-1@example.com"
gh auth login

export GH_REPO=itdojp/ae-framework
export AGENT_ROLE="role:IMPL-MED-1"
# Optional
export AE_FEATURE_RECONCILE=1
```

Typical role split:
- `PM-HIGH`: priority, sprint control, approval, weekly summary
- `ARCH-HIGH`: design, RFCs, interface definition, difficult review and approval
- `IMPL-MED-1/2/3`: child issue implementation, tests, CI, docs, and peer review

### 4) Slash command operations
Representative flow:
- `/start` -> move to `status:in-progress`, create or prepare draft work, assign owner if configured
- `/plan` -> inject checklist or execution notes into the PR body when that automation exists
- `/ready-for-review` -> move to `status:review`, request the configured review route
- `/approve-arch` and `/approve-pm` -> participate in merge-readiness signaling when the repository enables those commands
- `/block <reason>` and `/unblock` -> toggle blocked state

Current repository note:
- command ownership should stay explicit between `slash-commands.yml` and `agent-commands.yml`
- for issue-side automation, `agent-commands.yml` is the primary reference in the current baseline

### 5) Optional local watcher
A minimal polling example for an agent-specific queue:

```bash
#!/usr/bin/env bash
set -euo pipefail
while true; do
  gh issue list --repo "$GH_REPO" \
    --label "$AGENT_ROLE" --label status:ready \
    --json number,title,url | jq -r '.[] | .number' | while read -r N; do
      gh issue comment "$N" --body "/start"
      # Branch creation and draft PR creation can be left to Actions.
    done
  sleep 60
done
```

### 6) Guardrails and best practices
- use `feat/<issue>-<slug>` naming for short-lived branches
- keep PRs small enough to review quickly. Around 300 lines is a practical upper bound, not a hard rule
- use Conventional Commits with `Refs #<issue>` when appropriate
- stage DoD enforcement from warning to blocking rather than enabling strict blocking immediately
- prefer new files and narrow hooks first, then fold logic inward after the path stabilizes

### 7) Quick verification flow
1. create labels and milestones
2. attach `status:ready` and a role label to a child issue
3. run `/start` and confirm draft work begins on the expected path
4. run `/ready-for-review` and confirm review routing and required checks behave as expected
5. merge and confirm the linked issue closes or transitions as intended

### 8) Troubleshooting
- insufficient Actions permission -> Settings -> Actions -> General -> "Read and write permissions"
- CODEOWNERS not taking effect -> verify path patterns, owner names, and branch protection review requirements
- required checks not appearing -> verify workflow presence, trigger conditions, and workflow permissions
- command handling mismatch -> confirm whether the command is owned by `slash-commands.yml` or `agent-commands.yml`

## 日本語

### 概要
本ドキュメントは、PM、設計、実装担当などの複数エージェントが、GitHub 上のシグナルのみで計画、実装、レビュー、マージ、レポートまで連携するためのセットアップ手順を示します。前提は、各エージェントが同一マシン上、典型的には WSL2 Ubuntu 上の別ワークスペースで稼働することです。

ローカルで subagent を並行稼働させる場合の安全運用は本書では扱いません。`docs/agents/multi-agent-safety.md` と `docs/maintenance/subagent-worktree-runbook.md` を一次情報として参照してください。

### 前提
- branch protection と Actions 設定を変更できる repository administrator 権限
- `gh`、`git`、Node.js、`pnpm`
- 各エージェントごとのワークスペース。例: `~/ws/pm-high`、`~/ws/arch-high`、`~/ws/impl-1`

### 1) GitHub 側セットアップ

#### ラベル（役割、状態、スプリント、エピック）
作成例:

```bash
gh label create "role:PM-HIGH" --color C2F5FF || true
gh label create "role:ARCH-HIGH" --color C2F5FF || true
gh label create "role:IMPL-MED-1" --color C2F5FF || true
gh label create "role:IMPL-MED-2" --color C2F5FF || true
gh label create "role:IMPL-MED-3" --color C2F5FF || true

gh label create "status:ready" --color D4F8D4 || true
gh label create "status:in-progress" --color FFE8A3 || true
gh label create "status:review" --color A3D8FF || true
gh label create "status:blocked" --color FFBCBC || true
gh label create "status:done" --color CCCCCC || true

gh label create "sprint:0" --color EAEAEA || true
gh label create "sprint:1" --color EAEAEA || true
gh label create "sprint:2" --color EAEAEA || true
gh label create "sprint:3" --color EAEAEA || true

gh label create "epic:#898" --color EAEAEA || true
gh label create "epic:#701" --color EAEAEA || true
gh label create "epic:#786" --color EAEAEA || true
gh label create "epic:#879" --color EAEAEA || true
```

#### マイルストーン（スプリント）
```bash
gh api repos/:owner/:repo/milestones -X POST -f title='Sprint 0' -f state='open' || true
gh api repos/:owner/:repo/milestones -X POST -f title='Sprint 1' -f state='open' || true
gh api repos/:owner/:repo/milestones -X POST -f title='Sprint 2' -f state='open' || true
gh api repos/:owner/:repo/milestones -X POST -f title='Sprint 3' -f state='open' || true
```

#### `main` の branch protection
Settings -> Branches -> Branch protection rules で設定します。

推奨 baseline:
- review approval と、必要に応じた CODEOWNERS review を必須化する
- 現在の PR lane で required として扱う `verify-lite`、`policy-gate`、`gate` を登録する
- repository の review topology と整合する merge policy を維持する

#### CODEOWNERS（レビュー経路）
`.github/CODEOWNERS` 例:

```text
policy/** @org/arch-team
quality/** @org/arch-team
packages/spec-compiler/** @org/arch-team
docs/** @org/pm-team
```

現行 repository の注記:
- 現在の repository では、既定 path と上記の explicit path は `@ootakazuhiko` にルーティングされています
- 将来 team routing へ切り替える場合は、`.github/CODEOWNERS` と本書を同時に更新してください

#### PR template
`.github/pull_request_template.md` には、目的、スコープ、受け入れ条件、影響、リスク、rollback、関連 issue の確認項目を用意します。

#### GitHub Actions の最小構成
現行 baseline の最小 workflow:
- `triage.yml`: issue event で status / role label を正規化する
- `slash-commands.yml`: optional な issue_comment command entrypoint。issue 側 slash command が必要な場合にのみ有効化する
- `agent-commands.yml`: 現在の repository で issue 側 automation を主担当する command handler
- `verify-lite.yml`: required な軽量 verification lane
- `quality-gates-centralized.yml`: centralized quality gate runner

現行 repository の注記:
- `pr-quality.yml` は current baseline には含まれません
- 品質と merge gate は `verify-lite.yml` と `quality-gates-centralized.yml` で扱います
- progress summary や model evaluation のような後続 workflow は、既に有効な前提ではなく追加導入として扱ってください

> 注意: workflow が label、comment、issue / PR metadata を更新する必要がある場合、Settings -> Actions -> General で "Read and write permissions" を設定してください。

### 2) 推奨する最小 repository 構成
- `.github/CODEOWNERS`
- `.github/pull_request_template.md`
- `.github/workflows/triage.yml`
- `.github/workflows/slash-commands.yml`
- `.github/workflows/agent-commands.yml`
- `.github/workflows/verify-lite.yml`
- `.github/workflows/quality-gates-centralized.yml`
- `policy/quality.json`。DoD gate を warning から blocking へ段階導入するために使います

### 3) 各エージェントのワークスペース準備（WSL）
共通セットアップ例:

```bash
mkdir -p ~/ws/{pm-high,arch-high,impl-1,impl-2,impl-3}
cd ~/ws/impl-1 && gh repo clone itdojp/ae-framework
git config user.name "agent-impl-1"
git config user.email "agent-impl-1@example.com"
gh auth login

export GH_REPO=itdojp/ae-framework
export AGENT_ROLE="role:IMPL-MED-1"
# 必要に応じて
export AE_FEATURE_RECONCILE=1
```

典型的な役割分担:
- `PM-HIGH`: priority、sprint control、approval、週次 summary
- `ARCH-HIGH`: design、RFC、interface definition、難所 review と approval
- `IMPL-MED-1/2/3`: child issue 実装、test、CI、docs、peer review

### 4) スラッシュコマンド運用
代表的な flow:
- `/start` -> `status:in-progress` へ遷移し、必要に応じて draft work を開始する
- `/plan` -> その automation が存在する場合、PR body に checklist や execution note を挿入する
- `/ready-for-review` -> `status:review` に遷移し、設定された review route を起動する
- `/approve-arch` と `/approve-pm` -> repository がその command を有効化している場合、merge readiness の signal として扱う
- `/block <reason>` と `/unblock` -> blocked state を切り替える

現行 repository の注記:
- command の担当は `slash-commands.yml` と `agent-commands.yml` で明確に分けてください
- issue 側 automation の一次情報は、現行 baseline では `agent-commands.yml` です

### 5) ローカル watcher（任意）
各 agent が自分の queue を自動取得する最小ポーラ例:

```bash
#!/usr/bin/env bash
set -euo pipefail
while true; do
  gh issue list --repo "$GH_REPO" \
    --label "$AGENT_ROLE" --label status:ready \
    --json number,title,url | jq -r '.[] | .number' | while read -r N; do
      gh issue comment "$N" --body "/start"
      # branch 作成と draft PR 作成は Actions 側へ委譲してよい。
    done
  sleep 60
done
```

### 6) ガードレール / ベストプラクティス
- branch 名は `feat/<issue>-<slug>` を使う
- PR は短時間で review できるサイズに保つ。300 行程度は practical upper bound であり hard rule ではありません
- 必要に応じて Conventional Commits と `Refs #<issue>` を使う
- DoD enforcement は最初から strict blocking にせず、warning から blocking へ段階導入する
- まずは新規 file と狭い hook で始め、運用が安定した後に内側へ統合する

### 7) 動作確認（クイック）
1. label と milestone を作成する
2. child issue に `status:ready` と role label を付与する
3. `/start` を実行し、想定した path で draft work が始まることを確認する
4. `/ready-for-review` を実行し、review routing と required checks が期待どおりに動くことを確認する
5. merge 後に linked issue が close または所定の状態へ遷移することを確認する

### 8) トラブルシュート
- Actions 権限不足 -> Settings -> Actions -> General -> "Read and write permissions"
- CODEOWNERS が効かない -> path pattern、owner 名、branch protection の review requirement を確認する
- required check が出ない -> workflow の存在、trigger 条件、workflow permissions を確認する
- command の担当が不明確 -> その command が `slash-commands.yml` と `agent-commands.yml` のどちらの責務かを確認する
