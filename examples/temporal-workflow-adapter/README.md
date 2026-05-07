# Temporal Workflow Adapter PoC

This standalone example is documented in `../../docs/integrations/TEMPORAL-WORKFLOW-INTEGRATION.md`.
It is intentionally excluded from the root pnpm workspace so Temporal SDK dependencies remain optional.

Quick start:

```bash
temporal server start-dev
pnpm --dir examples/temporal-workflow-adapter install
pnpm --dir examples/temporal-workflow-adapter run worker
pnpm --dir examples/temporal-workflow-adapter run start -- --scenario inventory-waiver --auto-approve
```
