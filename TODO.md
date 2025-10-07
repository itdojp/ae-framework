# TODO: AE-Framework Next Steps (2025-10-07)

## 1. Enhanced State Manager TypedArray 対応（対応中）
- [ ] `src/utils/enhanced-state-manager.ts` の TypedArray / ArrayBuffer / SharedArrayBuffer / DataView 復元強化（進行中）
  - [x] 既存テスト確認 (`reviveEntryData` 現状把握)
  - [x] 追加 TypedArray ケース（SharedArrayBuffer / DataView / Float32Array）テスト実装
  - [x] stringify 時のシリアライズ / revive 時の復元実装追加
  - [x] 追加テスト含め `pnpm vitest --run tests/unit/utils/enhanced-state-manager.test.ts` パス確認
  - [ ] PR 化とレビュー依頼 (未着手)

## 2. versionIndex 差分検証テスト
- [x] import/export の versionIndex 差分を検証するユニットテストを追加し、Stryker survivor (Math.min 変異など) を排除

## 3. scripts/mutation/run-enhanced-state-batches.sh 改善
- [x] 機能別 mutate バッチファイル（state import / snapshot / failure artifact 等）を整備し、各 quick run を 15 分以内に収まるよう調整

## 4. EnhancedStateManager helper 横展開 (#1079)
- [x] `tests/resilience/**` などで helper を導入し、`as any` を段階的に削減する (ユーティリティ/ユニットテストへ横展開済み)
- [ ] 進捗を #1079 へ反映

## 5. Verify Lite / Mutation quick 週次トラッカー更新 (#999/#1001/#1002/#1003)
- [x] 最新結果を Week2/3/4/5 トラッカーへ追記（Issue #999/#1001/#1002/#1003）
- [x] #997 の Week5 調整計画を更新（Issue コメント更新済み）

## 6. Mutation survivor backlog (#1080)
- [ ] 残項目（Buffer 判定 OR 変異、versionIndex 差分検証など）を解消する追加 PR を準備

## 7. Trace Envelope / Report Envelope 差分チェックのゲート化 (#1015 系)
- [ ] 生成差分のホワイトリスト整備とレビュー手順策定
- [ ] 必須ゲート昇格のワークフロー更新

## 8. spec-generate-model.yml 監視フロー (#1011/#1038 関連)
- [ ] TLA+ Spec → Generate → Conformance 最小ジョブの現状確認
- [ ] 失敗時の通知・分析フローを整備

## 9. #1013 / #1012 Phase C 整理
- [ ] EnhancedStateManager ミューテーション対策 / runtime 短縮 / パイプライン健全性 / ドキュメント同期の最終確認
- [ ] 対応完了内容を #1013 にコメントし、#1012 Phase C の棚卸し完了を報告

## 10. #1011 Step3 着手準備
- [ ] 共通トレーススキーマ (NDJSON/OTLP) の設計 & ドキュメント化
- [ ] Projector PoC（ログ → 仕様状態）実装とテスト
- [ ] Validator PoC（TLC/Apalache 駆動）実装とテスト
- [ ] 上記成果を #1011 にコメント連携し、Step3 ブロッカーが無いことを確認

