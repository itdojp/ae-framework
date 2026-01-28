# Issue #1006: Setup Wizard Draft (Month 3)

## ステータス
- Draft: 2026-01-28
- 対象: Month 3
- 関連: Issue #1160 (DX/CLI 整備), docs/notes/issue-1006-dx-roadmap.md

## 目的
- 初期導入時の「何から始めるか」を CLI 上で明示し、導線を短縮する。
- テンプレート選定・依存導入・設定生成を一貫フローとして提供する。

## 前提/根拠
- 既存実装: `src/utils/installer-manager.ts` がテンプレート定義と導入処理を提供。
- 既存 CLI: `src/commands/extended/installer-command.ts` は `/ae:installer` として利用可能。
- CLI 実装は `commander`（`src/cli/index.ts`）で、対話 UI ライブラリは未採用。

## スコープ
- 新コマンド: `ae setup` を CLI に追加（Month 3 の最小セット）。
- 機能: テンプレート一覧/提案/導入の 3 種。
- 実行基盤: `InstallerManager` を直接呼び出し、既存テンプレートを利用。

## 非スコープ
- 対話 UI（TUI/GUI）やウィザード画面の導入。
- 外部テンプレートレジストリやリモート取得。
- 既存テンプレート仕様の全面的な再設計。

## CLI 仕様（案）
```
ae setup list
  - 既存テンプレート一覧を表示

ae setup suggest
  - 既存プロジェクトを解析し候補を提示

ae setup <template-id> [options]
  - テンプレートを導入

options:
  --name <projectName>
  --package-manager <npm|yarn|pnpm>
  --root <path>            (default: cwd)
```

## UX フロー（最小セット）
1) `ae setup list` でテンプレート一覧を把握。
2) `ae setup suggest` で推奨テンプレートを確認。
3) `ae setup <template-id>` で導入実行。
4) 成功時は作成ファイル/導入依存/次アクションを要約表示。

## 実装方針
- `src/cli/index.ts` に `createSetupCommand()` を追加。
- 依存注入ではなく `InstallerManager` を直接生成（小粒度）。
- `InstallerManager` の `prepareContext()` に任せ、package manager は既存検出を優先。
- 失敗時はエラー内容を CLI に整形出力して終了コードを返す。

## リスクと緩和
- 既存リポジトリでの導入: package.json への追記が発生。
  - 初期版は明示実行のみで回避（暗黙実行はしない）。
- 大きな依存導入: CI/ローカル環境に影響。
  - 失敗時にどのコマンドが失敗したかを出力する。

## 今後の拡張（Phase 2+）
- 対話プロンプト導入（テンプレート選択/上書き確認）。
- `--dry-run` / `--skip-install` オプション追加。
- テンプレートのローカル拡張/registry 連携。

## DoD
- 本ドキュメントを公開し、Month 3 の実装範囲を合意済み。
- Step2（最小実装）で `ae setup list/suggest/<template>` が動作可能。
