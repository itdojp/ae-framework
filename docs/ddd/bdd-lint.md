# BDD Lint: Aggregate Root Commands Only

- Rule: `When` steps must call an Aggregate Root command.
- Violation: CI fails with a suggested fix.
- Example (ok): `When the InventoryItem is allocated`.
- Example (violation): `When the Reservation is recalculated` (not a root command).

## Violations & Remedies
- NG: `When the Reservation is recalculated` (not an Aggregate Root command).
  - Remedy: introduce a root-level command e.g., `When the InventoryItem is recalculated` or refactor the flow via the root.
- NG: `When onHand is directly set to -1` (state mutation).
  - Remedy: use a command such as `When the InventoryItem is adjusted by -1`, then assert invariants.
