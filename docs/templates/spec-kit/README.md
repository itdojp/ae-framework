# Spec Kit Templates

> 🌍 Language / 言語: English | 日本語

---

## English (summary)

Spec Kit templates standardize the **spec-first** inputs for feature/bug/refactor work.
They are designed to reduce Context Vacuum and to make verify-then-merge practical.

- Feature: Gherkin/OpenAPI + error vocabulary + invariants + acceptance
- Bugfix: reproduction + logs + failing test + expected behavior
- Refactor: invariants + constraints + safety checks

---

## 日本語（概要）

Spec Kit は「仕様を一次情報として固定する」ためのテンプレ群です。
Context Vacuum を抑制し、verify-then-merge を成立させることを目的にしています。

- Feature: Gherkin/OpenAPI + エラー語彙 + 不変条件 + 受け入れ基準
- Bugfix: 再現手順 + ログ + failing test + 期待挙動
- Refactor: 不変条件 + 制約 + 安全性チェック

## 使い方

1. 目的に合わせてテンプレを選ぶ
2. 空欄を埋めて Spec Kit を完成させる
3. Spec Kit をもとに実装/テスト/CIゲートを計画する

## Templates

- `feature-spec-kit.md`
- `bugfix-spec-kit.md`
- `refactor-spec-kit.md`
