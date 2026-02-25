# Docs Doctest Policy

最終更新: 2026-02-25

## 目的

- PR のドキュメント検証を短時間で安定実行する
- 全量ドキュメント検証を定期実行に分離し、検証品質を維持する

## 実行スコープ

| レーン | トリガ | 実行内容 |
| --- | --- | --- |
| `doctest-index` | `pull_request` / `push(main)` / `workflow_dispatch` | `check-doc-consistency` + `../../README.md` / `../README.md` の doctest。`pull_request` では差分 Markdown も追加検証 |
| `doctest-full` | `schedule` / `workflow_dispatch(full=true)` | `docs/**/*.md` の全量 doctest |

Workflow: `.github/workflows/docs-doctest.yml`

## 運用ルール

1. PR では index スコープを基本とし、レビュー待ち時間を抑える
2. 全量チェックは週次 schedule で実行し、広域回帰を検知する
3. 全量結果の確認が必要な場合は `workflow_dispatch` で `full=true` を指定して再実行する
4. `scripts/ci/check-docs-doctest-policy-sync.mjs` を先行実行し、workflow / package script / policy の整合ドリフトを早期検出する

## 失敗時の対応手順（runbook）

1. 失敗ジョブを特定する（`doctest-index` / `doctest-full`）
2. ログから失敗種別を確認する
   - `Code blocks` の失敗: 該当 Markdown のコードブロックを修正
   - `Invalid Links` の失敗: リンク先の修正または URL 更新
3. ローカル再現する
   - index 失敗時: `DOCTEST_ENFORCE=1 pnpm run test:doctest:index`
   - full 失敗時: `DOCTEST_ENFORCE=1 pnpm run test:doctest:full`
4. 修正後、同一 run の `Re-run failed jobs` か、PR へ追 commit を push して再実行する

## ローカル実行コマンド

```bash
node scripts/ci/check-docs-doctest-policy-sync.mjs
pnpm run check:doc-consistency
pnpm run check:ci-doc-index-consistency
DOCTEST_ENFORCE=1 pnpm run test:doctest:index
DOCTEST_ENFORCE=1 pnpm run test:doctest:full
```
