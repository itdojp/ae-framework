# CodeX: OpenAPI → Contract/E2E Templates, Quickstart Quality Controls (2025-08-31)

This change adds contract/E2E test template generation from OpenAPI and improves the CodeX quickstart developer experience.

## Highlights
- Contract/E2E templates generator:
  - Script: `scripts/codex/generate-contract-tests.mjs`
  - Input: OpenAPI (`.yaml` or `.json`)
  - Output: `tests/api/generated/*.test.ts` (skipped test templates)
  - Summary: `artifacts/codex/openapi-contract-tests.json`
- Quickstart improvements:
  - `CODEX_SKIP_QUALITY=1` to skip quality gates
  - `CODEX_TOLERANT=1` to always exit 0 (non-blocking demo)
  - Enrich OpenAPI with minimal `/health` endpoint when `paths` is empty
- CI/Docs updates:
  - PR verify prints template counts when present
  - Integration docs list new env vars and artifacts

## Related
- Closes #292 (Docs: Update CodeX integration to reflect current adapter status and build prerequisites)
- Refs #295 (Generate contract/E2E test templates from OpenAPI in CodeX flow)

## Usage
```bash
pnpm run build
CODEX_SKIP_QUALITY=1 CODEX_RUN_FORMAL=1 pnpm run codex:quickstart
# Generated tests in tests/api/generated/, summary in artifacts/codex/openapi-contract-tests.json
```
