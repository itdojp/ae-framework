# Context Vacuum Checklist

> 🌍 Language / 言語: English | 日本語

---

## English (summary)

Use this checklist to ensure the minimum required context is present before delegating to LLM/agents.
If any item is missing, add **open questions** or **assumptions** to the Context Bundle.

---

## 日本語（チェックリスト）

### 1) 依存関係
- [ ] 呼び出し元・被呼び出し元が分かる
- [ ] 影響するモジュール/ファイルが特定できる

### 2) データ構造
- [ ] 入力/出力の型・形式が明示されている
- [ ] 主要フィールドの意味が説明されている

### 3) 実行文脈
- [ ] CLI/HTTP/CI の入口が明確
- [ ] 実行手順/環境（Node/OS/フラグ）が記載されている

### 4) 期待挙動
- [ ] 期待される成功/失敗条件が書かれている
- [ ] エラー語彙（エラー名/メッセージ）が定義されている

### 5) 検証可能性
- [ ] テストで検証できる基準が明示されている
- [ ] 再現手順またはサンプル入力がある

### 6) 既知の欠落
- [ ] 不足情報は `openQuestions` に列挙した
- [ ] 仮定は `assumptions` に明示した

---

## 関連
- `docs/guides/context-bundle.md`
- `schema/context-bundle.schema.json`
