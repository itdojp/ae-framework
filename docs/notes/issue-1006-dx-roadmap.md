# Issue #1006: DX Roadmap v1 (Month 3)

## ステータス
- v1 確定: 2026-01-26
- 対象: Month 3
- 参考PR: #1752 #1776

## 目的
- コマンド発見性の改善
- 移行期間の互換性維持と警告表示
- 統一 CLI の入口設計

## 入力
- docs/notes/issue-1006-script-migration-plan.md
- docs/notes/issue-1006-script-alias-map.md
- docs/notes/issue-1006-runner-interface.md
- docs/notes/issue-1006-script-inventory.md

## 施策（確定）
### 1) 統一 entry（scripts/<category>/run.mjs）
- 既存の draft CLI 仕様（--profile/--list/--dry-run）を実装
- category: test/quality/verify/flake/security から開始
- 既存スクリプトは alias で段階移行

### 2) alias と deprecation
- scripts/admin/script-alias-map.json を source of truth とし、legacy 名からの実行時に警告を出す
- 警告文に置換先と移行期限を明記

### 3) discovery 改善
- pnpm run help でカテゴリ別一覧と推奨エントリを提示
- (任意) `ae help` で CLI 側から同等の情報を提示

### 4) setup/guide
- 既存ドキュメントの統一（USAGE/CLI reference を一本化）
- 変更点が多い箇所には migration guide を併設

## 完了条件（DoD）
- 統一 CLI 入口（ae/ae-framework）から category runner（test/quality/verify/flake/security）へ到達できる
- help 出力に新旧コマンド対応表を明示し、警告メッセージに移行期限を表示
- docs: USAGE/CLI reference を統一し、移行ガイドを公開

## 実装順序
1) entry runner の統合パスを CLI から呼び出せるようにする
2) alias 警告を定型化し、移行期限を追加
3) `pnpm run help` と `ae help` を同期
4) docs の統一と migration guide を公開

## 進捗 (2026-01-28)
- [x] test/quality/verify/flake/security の entry script を用意
- [x] alias map を参照し legacy 実行時に警告 + 転送
- [x] `pnpm run help` のカテゴリ/推奨エントリ表示（既存）
- [x] 統一 CLI 入口から entry runner へルーティング（`ae entry <category>` で接続）
- [ ] docs の統一/移行ガイド整備

## リスクと対策
- 互換性: alias による後方互換 + 段階的削除
- 可観測性: help 出力の変更前後で差分を記録
