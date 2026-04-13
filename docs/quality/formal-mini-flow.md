---
docRole: derived
canonicalSource:
- docs/quality/formal-runbook.md
- docs/quality/formal-tools-setup.md
lastVerified: '2026-04-14'
---
# Formal Mini Flow: Counterexample -> Failing Test -> Fix -> Green

> 🌍 Language / 言語: English | 日本語

---

## English

### Purpose

- A minimal loop for connecting formal specs and implementation through small, repeatable steps.

### Example flow

1. Define the spec or expectation (TLA+, Alloy, or invariants).
   - Minimal TLA+: `spec/tla/DomainSpec.tla` with an invariant.
   - Minimal Alloy: `spec/alloy/Domain.als` with a safety assertion.
   - Implementation-side invariant: `onHand >= 0`, `allocated <= onHand` checked with `verify:conformance`.
2. Run the checker and obtain a counterexample.
   - `pnpm run spec:check:tla` or run `check` in Alloy IDE for `Domain.als`.
   - `pnpm run verify:conformance -i <events.json>`
3. Turn the counterexample into a failing test (Red).
   - Add the failing event sequence or input into `tests/` as the minimal reproduction.
4. Apply the smallest fix (Green).
   - Change the implementation only enough to make the failing test pass.
5. Refactor.
   - Remove duplication and reduce incidental complexity between spec and implementation.

### Helper commands

- TLA+ check: `pnpm run spec:check:tla` (runs when Apalache or TLC is available)
- Alloy check: `pnpm run spec:check:alloy` (shows guidance when CLI is unavailable)
- Trace validation: `pnpm run trace:validate` (lightweight schema consistency check)
- Conformance: `pnpm run verify:conformance [-i file --disable-invariants ...]`

### Tips

- Start with safety invariants first and keep the loop small.
- CI runs via the `run-formal` label in non-blocking mode.
- See `docs/quality/formal-runbook.md` and `docs/quality/formal-gates.md` for the full operating model.

## 日本語

### 目的

- 形式仕様と実装を小さなループで接続するための最小手順です。

### 基本フロー

1. 仕様 / 期待を定義します（TLA+ / Alloy / 不変条件）。
   - TLA+ 最小: `spec/tla/DomainSpec.tla` で不変条件を定義
   - Alloy 最小: `spec/alloy/Domain.als` で安全性アサーションを定義
   - 実装側の不変条件: `onHand >= 0`, `allocated <= onHand` を `verify:conformance` で確認
2. 実行して反例を得ます。
   - `pnpm run spec:check:tla`、または Alloy IDE で `Domain.als` を `check`
   - `pnpm run verify:conformance -i <events.json>`
3. 反例を失敗テストへ変換します（Red）。
   - 反例になったイベント列 / 入力を `tests/` に最小再現として追加する
4. 最小修正を適用します（Green）。
   - 失敗テストが通る最小限の修正だけを実装へ入れる
5. リファクタリングします。
   - 仕様と実装の重複や偶発的な複雑性を整理する

### 補助コマンド

- TLA+ チェック: `pnpm run spec:check:tla`（Apalache または TLC が使える場合に実行）
- Alloy チェック: `pnpm run spec:check:alloy`（CLI が使えない場合はガイダンスを表示）
- トレース検証: `pnpm run trace:validate`（軽量なスキーマ整合性チェック）
- Conformance: `pnpm run verify:conformance [-i file --disable-invariants ...]`

### 運用メモ

- まず安全性不変条件から始め、ループを小さく保ちます。
- CI は `run-formal` ラベルで非ブロッキングに起動します。
- 詳細な運用モデルは `docs/quality/formal-runbook.md` と `docs/quality/formal-gates.md` を参照してください。
