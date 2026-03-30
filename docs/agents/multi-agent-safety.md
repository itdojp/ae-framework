---
docRole: ssot
lastVerified: '2026-03-31'
owner: agent-ops
verificationCommand: pnpm -s run check:doc-consistency
---

# Multi-Agent Safety Policy

> 🌍 Language / 言語: English | 日本語

---

## English

### Overview
This document is the SSOT for safe use of `spawn_agent` and subagents in this repository. Its purpose is to prevent unexpected edits, commits, or branch mutations from leaking into a shared branch or shared worktree.

### Most important policy
- do not use subagents for write operations in this repository
- restrict subagent usage to read-only investigation
- allow only the main agent to perform commit, push, PR creation or update, and issue update

### Terms in this document
- `spawn_agent`: a call where the main agent starts a subagent and isolates the assignment into a dedicated worktree
- `explorer`: a subagent category used for investigation and exploration; regardless of the name, once repo context is provided it must be treated as potentially able to modify files

### Background
- subagents do not provide a guaranteed read-only execution model
- a repo-aware subagent, including an `explorer`, can still mutate files
- Git author identity can be identical across the main agent and subagents, so commit metadata alone is not enough for root-cause attribution

For that reason, this repository assumes that a subagent is capable of making changes and isolates it accordingly. Operationally, however, the policy is stricter: do not grant write work and use subagents only for read-only investigation.

### Invariants
1. any subagent that touches the repository gets a dedicated worktree, even for analysis-only work
2. subagents are not allowed to write in this repository
3. never let multiple agents share ownership of the same branch or worktree at the same time
4. every subagent assignment must state the target files, prohibitions, and completion criteria explicitly
5. after a subagent reports completion, the main agent must inspect the diff before allowing any commit, push, PR update, or issue update

### Role classification
| Category | Worktree | Allowed | Prohibited | Typical use |
| --- | --- | --- | --- | --- |
| analysis-only subagent | required | reading and returning notes to the main agent | editing repo files, commit, push, PR or issue update | code search, failure triage |
| implementation subagent | not used | none | edit, commit, push, PR or issue update | prohibited by current repository policy |
| main agent | optional | integration, editing, commit, push, PR update | delegating without a clear ownership boundary | final review, merge decision |

### Notes
- notes from an analysis-only subagent stay in the CLI response or the main agent report; do not save them into repository files, including dedicated worktrees
- implementation subagents remain suspended until write capability can be prevented technically, for example by a dedicated sandbox
- the default is to deny commit, push, PR update, and issue update to every subagent

### Request template
Every subagent request must include at least the following:
1. working location: absolute path of the dedicated worktree
2. investigation scope: files and directories that may be read
3. prohibitions: repository file changes, commit, push, PR or issue update, and access to other worktrees
4. completion criteria: expected deliverable and the confirmation commands to run
5. incident behavior: stop and report when unexpected changes or conflicts are found

Example:

```text
Assigned worktree: /home/devuser/work/CodeX/ae-framework-foo-agent1-wt
Scope: docs/agents/*, docs/maintenance/subagent-worktree-runbook.md
Prohibited: repository file changes, commit, push, PR or issue update, moving to other worktrees
Completion criteria: report git status --short and git diff --stat after the task
Incident behavior: stop and report if unexpected changes or conflicts are found
```

### Post-run checks
The main agent must always run the following after a subagent finishes:

```bash
git -C <worktree> status --short
git -C <worktree> diff --stat
git -C <worktree> log -1 --decorate
```

Check the following points:
- no changes outside the assigned scope
- no unauthorized commit, push, PR update, or issue update
- the reported work is consistent with the task instructions
- the source branch for any candidate change is explicit

### Incident handling
Stop immediately if any of the following occurs:
- `HEAD` of a shared worktree advanced unexpectedly
- changes outside the assigned scope were introduced
- a subagent performed commit, push, PR creation or update, or issue creation or update
- it is no longer possible to tell which agent produced the diff

After stopping, collect `git status`, `git log`, and `git reflog` from the affected worktree, then let the main agent decide whether the diff should be adopted or discarded.

Default response:
1. isolate the affected worktree or branch
2. treat the diff as discard-candidate until reviewed
3. have the main agent re-review the diff, validation result, and PR state
4. keep only the changes that are explicitly approved for adoption

### Related documents
- concrete create and cleanup procedure: `docs/maintenance/subagent-worktree-runbook.md`
- documentation responsibility boundary: `docs/agents/agents-doc-boundary-matrix.md`
- stale worktree cleanup: `docs/maintenance/worktree-cleanup-runbook.md`

## 日本語

### 概要
この文書は、`spawn_agent` / subagent を使う際の安全運用ルールの SSOT です。目的は、共有 branch / 共有 worktree 上で想定外の変更や commit が混入する事故を防ぐことです。

### 最重要方針
- 本リポジトリでは、subagent を書き込み作業に使わない
- subagent の用途は read-only 調査に限定する
- commit / push / PR 作成・更新 / Issue 更新は main agent だけが実行する

### 本書での用語
- `spawn_agent`: main agent が subagent を起動し、専用 worktree に作業を分離する呼び出し
- `explorer`: 調査・探索を主目的とする subagent 区分。名称にかかわらず、repo context を与えた時点で変更可能として扱う

### 背景
- subagent は read-only を保証しない
- `explorer` を含め、repo context を与えた subagent は変更を行う可能性がある
- Git の author 名は main agent / subagent で同一になる場合があり、commit metadata だけでは原因追跡に不十分である

このため、本リポジトリでは「subagent は変更可能」と仮定して隔離する。ただし運用ポリシーとしてはさらに厳格に、書き込みを許可せず、read-only 調査専用として扱う。

### 不変条件
1. repo に触れる subagent には、分析専用でも専用 worktree を割り当てる
2. 本リポジトリでは subagent に書き込みを許可しない
3. 共有 branch / 共有 worktree を複数 agent で同時所有しない
4. subagent には担当ファイル、禁止事項、完了条件を明示する
5. subagent 完了後、main agent が差分確認するまで commit / push / PR / Issue 更新を進めない

### 役割分類
| 区分 | worktree | 許可 | 禁止 | 典型例 |
| --- | --- | --- | --- | --- |
| 分析専用 subagent | 必須 | 読み取り、main agent への返答用メモ作成 | repo 配下ファイル変更、commit、push、PR / Issue 更新 | コード探索、失敗原因切り分け |
| 実装 subagent | 使用しない | なし | 編集、commit、push、PR / Issue 更新 | 現在の repo policy では禁止 |
| main agent | 任意 | 統合、編集、commit、push、PR 更新 | 担当境界を曖昧にしたまま委譲 | 最終レビュー、反映判断 |

### 注記
- 分析専用 subagent のメモは、CLI 応答または main agent への報告本文として残し、専用 worktree を含む repo 配下ファイルへ保存しない
- 実装 subagent は当面停止する。専用 sandbox などで write を技術的に封じられるまで再開しない
- 既定値は「subagent に commit / push / PR / Issue 更新を許可しない」とする

### 依頼テンプレート
subagent には最低限、次を含めて依頼する。
1. 作業場所: 専用 worktree の絶対パス
2. 調査対象: 参照してよいファイル / ディレクトリ
3. 禁止事項: repo 配下ファイル変更、commit、push、PR / Issue 更新、他 worktree 参照
4. 完了条件: 期待する成果物、実行すべき確認コマンド
5. 異常時動作: 想定外変更や衝突を見つけたら停止して報告

例:

```text
担当 worktree: /home/devuser/work/CodeX/ae-framework-foo-agent1-wt
調査対象: docs/agents/*, docs/maintenance/subagent-worktree-runbook.md
禁止事項: repo 配下ファイル変更, commit, push, PR / Issue 更新, 他 worktree への移動
完了条件: 変更後に git status --short と git diff --stat を報告
異常時: 想定外変更や競合を見つけたら作業を止めて報告
```

### 完了後の確認
main agent は subagent 完了後に必ず以下を確認する。

```bash
git -C <worktree> status --short
git -C <worktree> diff --stat
git -C <worktree> log -1 --decorate
```

確認ポイント:
- 担当範囲外の変更がない
- 無断 commit / push / PR / Issue 更新がない
- 変更が task 指示と整合する
- 取り込み元 branch が明確である

### 異常時の扱い
以下に該当した場合は、その場で停止する。
- 共有 worktree の `HEAD` が意図せず進んだ
- 担当外ファイルの変更が混入した
- subagent が commit / push / PR 作成・更新 / Issue 作成・更新を行った
- どの agent が作成した差分か識別できない

停止後は、対象 worktree の `git status` / `git log` / `git reflog` を採取し、差分を採用するか破棄するかを main agent が判断する。

既定動作:
1. 対象 worktree / branch を隔離する
2. その差分を破棄候補として扱う
3. main agent が差分・検証結果・PR 状態を再レビューする
4. 明示的に採用判断したものだけを残す

### 関連文書
- 具体的な作成・回収手順: `docs/maintenance/subagent-worktree-runbook.md`
- 文書責務境界: `docs/agents/agents-doc-boundary-matrix.md`
- stale worktree の清掃: `docs/maintenance/worktree-cleanup-runbook.md`
