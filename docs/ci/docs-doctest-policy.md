# Docs Doctest Policy

最終更新: 2026-02-25

## 目的

- PR のドキュメント検証を短時間で安定実行する
- 全量ドキュメント検証を定期実行に分離し、検証品質を維持する

## 実行スコープ

| レーン | トリガ | 実行内容 |
| --- | --- | --- |
| `doctest-index` | `pull_request` / `push(main)` / `workflow_dispatch` | `check-doc-consistency` + `README.md` / `docs/README.md` の doctest |
| `doctest-full` | `schedule` / `workflow_dispatch(full=true)` | `docs/**/*.md` の全量 doctest |

Workflow: `.github/workflows/docs-doctest.yml`

## 運用ルール

1. PR では index スコープを基本とし、レビュー待ち時間を抑える
2. 全量チェックは週次 schedule で実行し、広域回帰を検知する
3. 全量結果の確認が必要な場合は `workflow_dispatch` で `full=true` を指定して再実行する

## ローカル実行コマンド

```bash
pnpm run check:doc-consistency
DOCTEST_ENFORCE=1 pnpm run test:doctest:index
DOCTEST_ENFORCE=1 pnpm run test:doctest:full
```
