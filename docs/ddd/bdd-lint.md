# BDD Lint: Aggregate Root Commands Only

- Rule: `When` steps must call an Aggregate Root command.
- Violation: CI fails with a suggested fix.
- Example (ok): `When the InventoryItem is allocated`.
- Example (violation): `When the Reservation is recalculated` (not a root command).
