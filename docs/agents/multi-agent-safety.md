# Multi-Agent Safety Policy

最終更新: 2026-03-06

この文書は、`spawn_agent` / subagent を使う際の安全運用ルールの SSOT です。
目的は、共有 branch / 共有 worktree 上で想定外の変更や commit が混入する事故を防ぐことです。

## 背景

- subagent は read-only を保証しません。
- `explorer` を含め、repo コンテキストを与えた subagent は変更を行う可能性があります。
- Git の author 名は main agent / subagent で同一になる場合があり、commit metadata だけでは原因追跡に不十分です。

このため、本リポジトリでは「subagent は変更可能」と仮定して隔離します。

## 不変条件

1. repo に触れる subagent には、分析専用でも専用 worktree を割り当てる。
2. 書き込み作業は `1 agent = 1 worktree = 1 branch` とする。
3. 共有 branch / 共有 worktree を複数 agent で同時所有しない。
4. subagent には担当ファイル、禁止事項、完了条件を明示する。
5. subagent 完了後、main agent が差分確認するまで commit / push / PR 更新を進めない。

## 役割分類

| 区分 | worktree | 許可 | 禁止 | 典型例 |
| --- | --- | --- | --- | --- |
| 分析専用 subagent | 必須 | 読み取り、調査メモ作成 | ファイル変更、commit、push | コード探索、失敗原因切り分け |
| 実装 subagent | 必須 | 指定ファイルの編集 | 担当外変更、無断commit、無断push | 小規模修正、テスト追加 |
| main agent | 任意 | 統合、commit、push、PR更新 | 担当境界を曖昧にしたまま委譲 | 最終レビュー、反映判断 |

注記:

- 実装 subagent に commit を許可する場合は、依頼文に明示した場合のみとします。
- 既定値は「subagent に commit / push を許可しない」です。

## 依頼テンプレート

subagent には最低限、次を含めて依頼します。

1. 作業場所: 専用 worktree の絶対パス
2. 担当範囲: 編集してよいファイル / ディレクトリ
3. 禁止事項: commit、push、担当外編集、他 worktree 参照
4. 完了条件: 期待する成果物、実行すべき確認コマンド
5. 異常時動作: 想定外変更や衝突を見つけたら停止して報告

例:

```text
担当 worktree: /home/devuser/work/CodeX/ae-frameworkA/ae-framework-foo-agent1-wt
担当ファイル: docs/agents/*, docs/maintenance/subagent-worktree-runbook.md
禁止事項: commit, push, 担当外ファイル編集, 他 worktree への移動
完了条件: 変更後に git status --short と git diff --stat を報告
異常時: 想定外変更や競合を見つけたら作業を止めて報告
```

## 完了後の確認

main agent は subagent 完了後に必ず以下を確認します。

```bash
git -C <worktree> status --short
git -C <worktree> diff --stat
git -C <worktree> log -1 --decorate
```

確認ポイント:

- 担当範囲外の変更がない
- 無断 commit がない
- 変更が task 指示と整合する
- 取り込み元 branch が明確

## 異常時の扱い

以下に該当した場合は、その場で停止します。

- 共有 worktree の `HEAD` が意図せず進んだ
- 担当外ファイルの変更が混入した
- subagent が commit / push を行った
- どの agent が作成した差分か識別できない

停止後は、対象 worktree の `git status` / `git log` / `git reflog` を採取し、
差分を採用するか破棄するかを main agent が判断します。

## 関連文書

- 具体的な作成・回収手順: `docs/maintenance/subagent-worktree-runbook.md`
- 文書責務境界: `docs/agents/agents-doc-boundary-matrix.md`
- stale worktree の清掃: `docs/maintenance/worktree-cleanup-runbook.md`
