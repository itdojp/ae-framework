# Issue #1006: DX Roadmap Draft (Month 3)

## 目的
- コマンド発見性の改善
- 移行期間の互換性維持と警告表示
- 統一 CLI の入口設計

## 入力
- docs/notes/issue-1006-script-migration-plan.md
- docs/notes/issue-1006-script-alias-map.md
- docs/notes/issue-1006-runner-interface.md
- docs/notes/issue-1006-script-inventory.md

## 施策案
### 1) 統一 entry（scripts/<category>/run.mjs）
- 既存の draft CLI 仕様（--profile/--list/--dry-run）を実装
- category: test/quality/verify/flake/security から開始
- 既存スクリプトは alias で段階移行

### 2) alias と deprecation
- scripts/admin/script-alias-map.json を source of truth とし、
  legacy 名からの実行時に警告を出す
- 警告文に置換先と移行期限を明記

### 3) discovery 改善
- pnpm run help でカテゴリ別一覧と推奨エントリを提示
- (任意) `ae help` で CLI 側から同等の情報を提示

### 4) setup/guide
- 既存ドキュメントの統一（USAGE/CLI reference を一本化）
- 変更点が多い箇所には migration guide を併設

## 進め方（案）
1) test/quality/verify/flake/security の entry script 雛形を作成
2) alias map を実装し、警告出力のみ先行
3) `pnpm run help` をカテゴリ表示へ拡張
4) docs で新旧コマンド対応表を明示

## リスクと対策
- 互換性: alias による後方互換 + 段階的削除
- 可観測性: help 出力の変更前後で差分を記録
