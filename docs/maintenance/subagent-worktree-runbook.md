# Subagent Worktree Runbook

最終更新: 2026-03-06

この runbook は、subagent ごとに専用 worktree を作成し、検証し、回収する標準手順を定義します。

## 適用範囲

- `spawn_agent` を用いる全作業
- 分析専用 / 実装の両方
- main agent が最終的に commit / push / PR 更新を担う運用

## 命名規約

- worktree path: `../ae-framework-<topic>-<agent>-wt`
- 一時 branch: `wip/<topic>-<agent>`
- PR 用 branch を直接使う場合でも、1 worktree に 1 branch の原則は維持する

例:

- worktree: `../ae-framework-2450-docs-agent1-wt`
- branch: `wip/2450-docs-agent1`

## 手順

### 1. ベース参照を決める

- PR 作業の追従なら対象 branch を base にする
- 新規作業なら通常 `origin/main` を base にする
- `<base-ref>` は worktree 作成元の ref を指す（例: `origin/main`, `origin/<pr-branch>`, `main`）
- `<base-ref>` が remote-tracking ref の場合は、対応する `<base-remote>` / `<base-branch>` を先に fetch して最新化する（例: `origin/main` -> `origin`, `main`）

### 2. 専用 worktree を作成する

```text
git fetch <base-remote> <base-branch> --quiet
git worktree add ../ae-framework-<topic>-<agent>-wt -b wip/<topic>-<agent> <base-ref>
```

例: `<base-ref>=origin/main` なら `git fetch origin main --quiet` を実行します。
`<base-ref>` が最新化済みのローカル ref の場合は、`git fetch` を省略して構いません。

確認:

```text
git -C ../ae-framework-<topic>-<agent>-wt status --short --branch
```

期待値は clean start です。

### 3. subagent へ担当範囲を割り当てる

依頼文に必ず以下を含めます。

- worktree の絶対パス
- 編集可能ファイル
- commit / push の可否
- 実行してよい検証コマンド
- 異常時停止条件

既定値:

- commit 禁止
- push 禁止
- 担当外編集禁止

### 4. subagent 完了後に検証する

```text
git -C ../ae-framework-<topic>-<agent>-wt status --short
git -C ../ae-framework-<topic>-<agent>-wt diff --stat
git -C ../ae-framework-<topic>-<agent>-wt log -1 --decorate
```

必要に応じて:

```text
git -C ../ae-framework-<topic>-<agent>-wt diff
git -C ../ae-framework-<topic>-<agent>-wt reflog -5
```

### 5. main agent が統合する

選択肢:

1. 差分を review して main agent が同一内容を再適用する
2. worktree branch から cherry-pick する
3. 差分を patch 化して適用する

既定値は 1 です。履歴の追跡が必要な場合のみ 2 を使います。

### 6. 回収する

統合後に不要になった worktree は回収します。

```text
git worktree remove ../ae-framework-<topic>-<agent>-wt
git branch -D wip/<topic>-<agent>
```

dirty で remove できない場合は、残差分を確認してから対処します。
stale worktree 一括清掃は `docs/maintenance/worktree-cleanup-runbook.md` を参照します。

## 異常系 runbook

### 想定外 commit が存在する

```text
git -C ../ae-framework-<topic>-<agent>-wt log --oneline --decorate -5
git -C ../ae-framework-<topic>-<agent>-wt show --stat --summary <commit>
```

対応:

- 採用する: diff を review して統合
- 採用しない: worktree を破棄し、必要なら作り直す

### worktree の HEAD が共有 branch を追い越した

shared branch 運用に戻らず、必ず専用 branch へ退避させてから整理します。

### 誰が変更したか識別できない

Git author 名では識別できない前提で、`reflog` と subagent 実行ログを一次情報として判断します。

## 運用チェックリスト

- [ ] subagent ごとの専用 worktree を作成した
- [ ] 担当ファイルと禁止事項を依頼文へ明記した
- [ ] 完了後に `status` / `diff --stat` / `log -1` を確認した
- [ ] main agent が統合判断を行った
- [ ] 不要 worktree を回収した
