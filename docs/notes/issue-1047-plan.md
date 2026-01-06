# Issue #1047 / #1053 現状整理メモ

## ゴール
- Agent Builder 互換の Intent→Operate フロースキーマと Envelope v1.0 を策定し、CI で常時検証できる状態にする。
- Verify Lite など既存パイプラインを Envelope へ変換し、Agent Builder アダプタと連携させる PoC を完成させる。

## 進行状況
- ✅ 要件・ロードマップは #1047 / #1053 で定義済み。
- ✅ Flow Schema / Envelope / Ajv CI などのベース実装は PR #1184/#1186/#1187 で整備済み。
- ✅ Agent Builder Adapter スケルトン（flow-runner + tests）は整備済み。
- ☐ Verify Lite PoC は未完（demo 実行手順の整備が残り）。

## 直近のアクション候補
1. ✅ PR-1: Flow Schema v0.1 + Envelope v1.0 + Ajv CI（#1184/#1186/#1187）。
2. ✅ PR-2: Verify Lite → Envelope 変換の実装とテスト（#1186）。
3. ✅ PR-3: Agent Builder Adapter スケルトン（flow JSON 取り込み・ノード実行モック・Envelope出力整合）。
4. 🔄 PR-4: Intent→Formal→Code→Verify PoC（Adapter + Verify Lite + Formal ツール連携での e2e 実験）。

## リスク
- スキーマ変更の影響 → semver 管理、スナップショットテスト。
- 形式仕様生成の自動化は研究課題 → 手動確認フローを残す。
- 多段パイプラインの非決定性 → 入出力のスクラブ、スタブ化の検討。
