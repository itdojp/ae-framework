# EnhancedStateManager Helper 展開ロードマップ

## 目的
`buildExportedState` / `buildStateEntry` を他のレガシーテスト（特に `tests/resilience` 系のバックアップシナリオ）へ横展開し、`as any` や ad-hoc JSON の使用を排除する。

## スコープ
- `tests/resilience/**` に存在する import/export 系テスト
- `scripts/mutation/**` で JSON を直接生成しているユーティリティ
- `docs/notes` の手順例で旧形式 JSON を参照している箇所

## 実施ステップ
1. `tests/resilience` で `buildExportedState` を import し、既存の `as any` を削減する。
2. 共通 fixture を `tests/fixtures/enhanced-state/*.ts` に切り出し、snapshot 的に再利用できるようにする。
3. stringify キャッシュ（`enableSerializationCache`）のメトリクスを検証する専用テストを追加して helper の恩恵を定量化する。
4. Mutation Quick の survivor 対応 Issue (#TODO) と連動させ、helper 展開によるスコア改善をトラッキングする。

## 次のアクション
- [ ] `tests/resilience/import-state.*` 系テストに helper を導入する PR を作成
- [ ] Fixtures ディレクトリの設計を `docs/notes/mutation-coverage-plan.md` に追記
- [ ] Mutation レポートで helper 適用箇所をタグ付けする
