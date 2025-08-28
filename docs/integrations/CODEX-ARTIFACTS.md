# CodeX Artifacts and JSON Formats

This document describes the machine-readable artifacts produced when running ae-framework phases via the CodeX adapter.

## Per-phase result files

- Path: `artifacts/codex/result-<phase>.json` (or directory in `CODEX_ARTIFACTS_DIR` if set)
- Format:
```jsonc
{
  "phase": "intent|formal|stories|validation|modeling|ui",
  "response": {
    "summary": "string",
    "analysis": "string",
    "recommendations": ["string"],
    "nextActions": ["string"],
    "warnings": ["string"],
    "shouldBlockProgress": true
  },
  "ts": "2025-01-01T00:00:00.000Z"
}
```

Notes:
- `response` follows the TaskResponse shape used across adapters.
- `analysis` may contain multi-line text; consumers should handle large strings safely.

## UI summary

- Path: `artifacts/codex/ui-summary.json`
- Format:
```json
{
  "totalEntities": 1,
  "okEntities": 1,
  "files": ["apps/web/app/products/page.tsx", "apps/web/components/ProductForm.tsx"],
  "dryRun": true,
  "artifactDir": "/abs/path/to/artifacts/codex"
}
```

## Formal artifacts

- TLA+ (if generated): `artifacts/codex/formal.tla`
- OpenAPI (if derived): `artifacts/codex/openapi.yaml`
- Model checking summary (best-effort):
  - Path: `artifacts/codex/model-check.json`
  - Shape aligns with FormalAgent `ModelCheckingResult`:
  ```json
  {
    "specification": "string",
    "properties": [
      { "name": "string", "satisfied": true, "description": "string", "counterExample": { "trace": [], "description": "string" } }
    ],
    "counterExamples": [ { "trace": [], "description": "string" } ],
    "statistics": { "statesExplored": 0, "timeElapsed": 0, "memoryUsed": 0 }
  }
  ```

## CI collection

The PR Verify workflow uploads:
- `codex-json-artifacts`: all `artifacts/codex/result-*.json`
- `codex-formal-tla`: `artifacts/codex/formal.tla` (if present)
- `codex-openapi`: `artifacts/codex/openapi.yaml` (if present)
- `codex-model-check`: `artifacts/codex/model-check.json` (if present)

Additionally, it posts a PR comment summarizing model check and UI scaffold results.
