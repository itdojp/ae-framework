# Formal Mini Flow: 反例 → 失敗テスト → 修正 → 緑

目的
- 形式仕様と実装の“接着”を小さいループで回すための最小手順。

流れ（例）
1) 仕様/期待を定義（TLA+/Alloy/不変）
   - TLA+ 最小: `spec/tla/DomainSpec.tla`（Invariant を定義）
   - Alloy 最小: `spec/alloy/Domain.als`（Safety アサーション）
   - 実装側の不変: onHand>=0, allocated<=onHand（verify:conformance でチェック）
2) 実行で反例が出る
   - `pnpm run spec:check:tla` ／ Alloy IDEで `Domain.als` を `check` 実行
   - `pnpm run verify:conformance -i <events.json>`
3) 反例をテスト化（Red）
   - 反例となるイベント列/入力を `tests/` に最小再現として追加
4) 実装を最小修正（Green）
   - 失敗テストが通るように、小さく修正
5) リファクタリング（Refactor）
   - 仕様と実装の重複/複雑性を整理

補助コマンド
- TLA+ チェック: `pnpm run spec:check:tla`（Apalache または TLC がある場合に実行）
- Alloy チェック: `pnpm run spec:check:alloy`（CLIがなければガイダンスを表示）
- トレース検証: `pnpm run trace:validate`（スキーマ整合の軽量チェック）
- Conformance: `pnpm run verify:conformance [-i file --disable-invariants ...]`

Tips
- まずは「不変（safety）」から始め、小さいループで回す
- CIは `run-formal` ラベルで起動（非ブロッキング）
- 詳細は `docs/quality/formal-runbook.md` と `docs/quality/formal-gates.md`

