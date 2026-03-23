---
docRole: derived
canonicalSource:
- docs/spec/context-pack.md
- docs/ci/ci-troubleshooting-guide.md
lastVerified: '2026-03-23'
---
# Context Vacuum Checklist

> 🌍 Language / 言語: English | 日本語

---

## English

Use this checklist before delegating to LLMs or agents. If any item is missing, record it explicitly in the Context Bundle as an **open question** or **assumption** instead of leaving it implicit.

### 1) Dependencies
- [ ] Callers and callees are identifiable
- [ ] The affected modules/files are identified

### 2) Data structures
- [ ] Input/output types or formats are documented
- [ ] The meaning of the main fields is described

### 3) Execution context
- [ ] The entry point is clear (CLI / HTTP / CI)
- [ ] Runtime steps and environment assumptions (Node / OS / flags) are written down

### 4) Expected behavior
- [ ] Success and failure conditions are written down
- [ ] Error vocabulary (error names / messages) is defined

### 5) Verifiability
- [ ] Verifiable test criteria are explicit
- [ ] A reproduction path or sample input exists

### 6) Known gaps
- [ ] Missing information is listed in `openQuestions`
- [ ] Provisional assumptions are listed in `assumptions`

### 7) DbC (Design by Contract)
- [ ] `contracts.preconditions` records input constraints and prerequisite state
- [ ] `contracts.postconditions` records observable post-state
- [ ] `contracts.invariants` records constraints that must always hold
- [ ] Each condition can be traced to a validating test / gate / evidence source

### Related
- `docs/guides/context-bundle.md`
- `schema/context-bundle.schema.json`

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

### 7) DbC（Design by Contract）
- [ ] `contracts.preconditions` に入力制約/前提状態を記載した
- [ ] `contracts.postconditions` に観測可能な事後状態を記載した
- [ ] `contracts.invariants` に常時成立する制約を記載した
- [ ] 各条件の検証先（test/gate/evidence）が追跡できる

---

## 関連
- `docs/guides/context-bundle.md`
- `schema/context-bundle.schema.json`
