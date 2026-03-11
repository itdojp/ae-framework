---
docRole: ssot
lastVerified: '2026-03-12'
owner: testing
verificationCommand: pnpm -s run check:doc-consistency
---

# BDD Lint: Aggregate Root Commands Only

> 🌍 Language / 言語: English | 日本語

---

## 日本語（概要）

Gherkin の `When` は集約ルートのコマンドのみを呼び出す、というリンタ規約です。違反時は CI を失敗させ、修正案を提示します。状態の直接変更を避け、ユビキタス言語とカプセル化を維持します。

- Rule: `When` steps must call an Aggregate Root command.
- Violation: CI fails with a suggested fix.
- Example (ok): `When the InventoryItem is allocated`.
- Example (violation): `When the Reservation is recalculated` (not a root command).

## Violations & Remedies
- NG: `When the Reservation is recalculated` (not an Aggregate Root command).
  - Remedy: introduce a root-level command e.g., `When the InventoryItem is recalculated` or refactor the flow via the root.
- NG: `When onHand is directly set to -1` (state mutation).
  - Remedy: use a command such as `When the InventoryItem is adjusted by -1`, then assert invariants.
## Rules Table
| Rule | OK | NG | Rationale |
|------|----|----|-----------|
| When uses Aggregate Root command | `When InventoryItem is allocated` | `When Reservation is recalculated` | Enforce invariants at root |
| No direct state mutation in When | `When InventoryItem is adjusted by -1` | `When onHand is set to -1` | Preserve Ubiquitous Language & encapsulation |
