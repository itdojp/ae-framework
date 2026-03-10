---
docRole: derived
canonicalSource:
  - docs/quality/ARTIFACTS-CONTRACT.md
  - docs/reference/CONTRACT-CATALOG.md
lastVerified: '2026-03-10'
---

# CodeX Artifacts and JSON Formats

> 🌍 Language / 言語: English | 日本語

---

## 日本語（概要）

CodeX アダプターで各フェーズを実行したときに生成される、機械可読な成果物の仕様をまとめています。

- フェーズごとの結果: `artifacts/codex/result-<phase>.json`（共通 `TaskResponse` 形）
- UI サマリ: `artifacts/codex/ui-summary.json`
- Formal 関連: `formal.tla`, `openapi.yaml`, `model-check.json`
- 契約/E2E テンプレート: `tests/api/generated/` と `openapi-contract-tests.json`
- CI 収集: PR Verify が主要成果物をアーティファクトとしてアップロード

以下の英語セクションに JSON 形や例が詳述されています。

This document describes the machine-readable artifacts produced when running ae-framework phases via the CodeX adapter.

## stdio adapter contract (`scripts/codex/adapter-stdio.mjs`)

- Input schema: `schema/codex-task-request.schema.json`
- Output schema: `schema/codex-task-response.schema.json`
- The adapter validates both stdin request JSON and adapter response JSON.

Exit code contract:
- `0`: success (`shouldBlockProgress=false`)
- `2`: success but blocked (`shouldBlockProgress=true`)
- `3`: invalid input (invalid JSON / request schema violation)
- `1`: internal error (adapter exception / schema load failure / invalid response schema)

Error response format (machine-readable):
```json
{
  "error": true,
  "code": "INVALID_REQUEST_SCHEMA",
  "message": "Request does not match codex task request schema",
  "details": {
    "schema": "schema/codex-task-request.schema.json",
    "errors": [
      { "path": "/subagent_type", "message": "must have required property 'subagent_type'" }
    ]
  },
  "ts": "2026-02-18T00:00:00.000Z"
}
```

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

## Generated contract/E2E test templates

When the quickstart runs with `CODEX_RUN_FORMAL=1` and an OpenAPI is produced, a generator creates Vitest templates:

- Tests directory: `tests/api/generated/`
- One file per operationId: `<operationId>.test.ts`
- Tests are `it.skip(...)` by default (safe templates to customize)
- Machine-readable summary: `artifacts/codex/openapi-contract-tests.json`

Example summary:
```json
{
  "openapi": "artifacts/codex/quickstart-openapi.yaml",
  "outDir": "tests/api/generated",
  "files": 12,
  "operations": [
    { "operationId": "getUser", "method": "get", "path": "/users/{id}", "file": "tests/api/generated/getUser.test.ts" }
  ],
  "mode": "templates",
  "ts": "2025-01-01T00:00:00.000Z"
}
```

## CI collection

The PR Verify workflow uploads:
- `codex-json-artifacts`: all `artifacts/codex/result-*.json`
- `codex-formal-tla`: `artifacts/codex/formal.tla` (if present)
- `codex-openapi`: `artifacts/codex/openapi.yaml` (if present)
- `codex-model-check`: `artifacts/codex/model-check.json` (if present)

Additionally, it posts a PR comment summarizing model check and UI scaffold results.
