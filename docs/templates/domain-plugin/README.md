# Domain Plug-in Template (Minimal)

This template describes how to create a Domain Plug-in for ae-framework.

- Goal: provide domain-specific hooks for spec → test/code generation, replay fixtures, and formal presets.
- Structure:
  - `plugin.json`: metadata (`name`, `version`, `description`)
  - `schemas/`: JSON Schemas for domain events/contracts (optional)
  - `presets/`: formal presets (TLA+/Alloy) and BDD step lint rules (optional)
  - `generators/`: code/test generators (optional)

Example `plugin.json`:
```
{
  "name": "@example/inventory-domain",
  "version": "0.1.0",
  "description": "Inventory domain plug-in for ae-framework",
  "schemas": ["schemas/domain-events.schema.json"],
  "presets": ["presets/tla-presets.json", "presets/bdd-lint.json"],
  "generators": ["generators/codegen.js", "generators/tests.js"]
}
```

Usage:
- Place the plug-in under `plugins/<your-domain>/`.
- Reference schemas/presets in Spec/CI workflows as needed.
- Keep changes small and label-gated; prefer report-only presets first.
