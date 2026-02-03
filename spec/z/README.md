# Z Notation Specs (Phase 0: doc-first)

> 🌍 Language / 言語: English | 日本語

Z is used here as a **readable but precise** document asset for domain state/invariants and operation pre/postconditions.
Tool execution (typechecking/consistency) is intentionally out-of-scope for Phase 0 because the best CI-friendly toolchain is not fixed yet.

## English

### Goals
- Keep a strict, reviewable spec of state + operations (pre/post) in Z notation.
- Cross-reference invariants/assertions used by other specs:
  - TLA+: `spec/tla/DomainSpec.tla`
  - Alloy: `spec/alloy/Domain.als`

### Files
- `domain/Domain.md`: minimal domain state + operations in LaTeX-ish Z (ASCII-only)

### Mapping (TLA+/Alloy/Z)

| Concern | TLA+ | Alloy | Z |
| --- | --- | --- | --- |
| Initial state | `Init` | `Init` | `InitDomainState` |
| Invariant | `Invariant` | `Invariant` / `assert Safety` | `DomainState` constraints (note: `onHand <= MaxOnHand` is TLA+/Z-only in Phase 0) |
| Receive/onHand increment | `Next` 1st branch | (not modeled) | `Receive` |
| Allocate increment | `Next` 2nd branch | (not modeled) | `Allocate` |
| Ship (decrement) | `Next` 3rd branch | (not modeled) | `Ship` |

Notes:
- For Phase 0, Z is a document asset. If/when a stable tool is selected, we will add a non-blocking runner and CI wiring.

---

## 日本語（概要）

このフォルダは、Z 記法を **仕様資産（ドキュメント）** として配置するための置き場です。状態（不変条件）と操作（事前/事後条件）をレビュー可能な形で厳密に記述し、TLA+/Alloy 等の仕様と相互参照できる状態にします。

### 現状（Phase 0）
- ツール実行（型検査/整合性チェック）の CI 統合は行いません（採用ツールが未確定のため）。
- 将来、採用ツールが確定した段階で non-blocking のランナーと CI 統合を追加します。

### ファイル構成
- `domain/Domain.md`: 最小のドメイン状態/操作を Z で記述（ASCIIのみ、LaTeX 風）

### 対応表（TLA+/Alloy/Z）

| 観点 | TLA+ | Alloy | Z |
| --- | --- | --- | --- |
| 初期状態 | `Init` | `Init` | `InitDomainState` |
| 不変条件 | `Invariant` | `Invariant` / `assert Safety` | `DomainState` の制約（注: `onHand <= MaxOnHand` は Phase 0 では TLA+/Z のみ） |
| 入庫（onHand 増加） | `Next` の第1分岐 | （未対応） | `Receive` |
| 引当（allocated 増加） | `Next` の第2分岐 | （未対応） | `Allocate` |
| 出庫（減少） | `Next` の第3分岐 | （未対応） | `Ship` |
