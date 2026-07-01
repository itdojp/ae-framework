# Domain assurance presets

This directory contains report-only starter presets for product archetypes where ae-framework evidence usually has high value.

- `web-api-bff/preset.json` — HTTP API/BFF changes that need Context Pack, ExecPlan, verify-lite, and PR assurance evidence.
- `event-driven-domain/preset.json` — event/replay/conformance-focused domains such as inventory, ordering, and payment workflows.
- `spec-led-brownfield/preset.json` — brownfield features imported from local Spec Kit-style artifacts.
- `high-assurance-critical-core/preset.json` — selected high-risk cores that justify formal/model/proof evidence.

Each `preset.json` conforms to `schema/domain-assurance-preset.schema.json` and remains report-only. Presets select starting inputs and evidence surfaces; they do not approve, merge, bypass Context Pack, bypass ExecPlan, or promote policy-gate enforcement.

Render a deterministic review surface for a preset:

```bash
pnpm run domain-presets:render -- \
  --preset templates/domain-presets/web-api-bff/preset.json \
  --generated-at 2026-07-01T00:00:00.000Z \
  --output-json artifacts/domain-presets/web-api-bff.json \
  --output-md artifacts/domain-presets/web-api-bff.md
```
