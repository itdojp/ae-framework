---
docRole: derived
canonicalSource:
  - docs/quality/ARTIFACTS-CONTRACT.md
  - docs/reference/CONTRACT-CATALOG.md
lastVerified: '2026-03-10'
---

# Codex Artifacts and JSON Formats

> 🌍 Language / 言語: English | 日本語

---

## 日本語（概要）

Codex アダプターで各フェーズを実行したときに生成される、機械可読な成果物の仕様をまとめています。

- フェーズごとの結果: `artifacts/codex/result-<phase>.json`（共通 `TaskResponse` 形）
- UI サマリ: `artifacts/codex/ui-summary.json`
- Formal scaffold 関連: `formal.tla`, `openapi.yaml`, `result-formal.json`
- 実 model-check Evidence: `pnpm run model-check` / `pnpm run verify:model` を明示実行した場合のみ `model-check.json`
- 契約/E2E テンプレート: `tests/api/generated/` と `openapi-contract-tests.json`
- CI 収集: PR Verify が主要成果物をアーティファクトとしてアップロード

以下の英語セクションに JSON 形や例が詳述されています。

This document describes the machine-readable artifacts produced when running ae-framework phases via the Codex adapter.

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
    "shouldBlockProgress": true,
    "formal": {
      "scaffold": { "status": "generated", "artifactStatus": "draft", "validationStatus": "valid", "artifactPath": "artifacts/codex/formal.tla" },
      "modelChecking": { "status": "not-run", "evidenceArtifact": null, "runnerCommands": ["pnpm run verify:tla -- --engine=tlc"] }
    }
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

## Formal scaffold and execution artifacts

- TLA+ (if generated): `artifacts/codex/formal.tla`
- OpenAPI (if derived): `artifacts/codex/openapi.yaml`
- `FormalAgent` and the Codex formal phase produce `artifactStatus=draft`. They perform structural generation/validation only and never create successful model-check evidence.
- `response.formal.modelChecking.status=not-run` and `evidenceArtifact=null` are required until an actual checker runner executes.
- Actual model-check report (only after explicit `pnpm run model-check` or `pnpm run verify:model`):
  - Path: `artifacts/codex/model-check.json`
  - Producer: `scripts/verify/run-model-checks.mjs`
  - `status=not-run` and `ok=null` when no checker input executes; this is not success evidence.
  - Per-attempt `executionStatus` distinguishes a completed checker process (`executed`) from `timeout` and startup/runtime `tool-error`. A completed checker that returns a counterexample or non-zero verification result remains `executionStatus=executed` with `outcome=fail`; it is not mislabelled as a tool error.
  - Each result records tool identity/version (or explicit `unknown` plus artifact SHA-256), input, result, bounded scope, and assumptions. Only `executionStatus=executed` can count as completed checker evidence:
  ```json
  {
    "schemaVersion": "model-check-report/v1",
    "artifactStatus": "execution-report",
    "status": "executed|failed|tool-error|not-run",
    "ok": true,
    "alloy": {
      "results": [{
        "executionStatus": "executed",
        "evidence": {
          "tool": { "name": "Alloy", "version": "unknown", "artifactSha256": "<sha256>" },
          "input": { "specification": "spec/formal/model.als", "configuration": null },
          "result": { "outcome": "pass", "exitCode": 0, "log": "artifacts/codex/model.alloy.log.txt" },
          "scope": { "kind": "alloy-model", "identifier": "model" },
          "assumptions": ["The result applies only to the bounds and commands declared by the supplied Alloy model."]
        }
      }]
    }
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
- `codex-model-check`: actual-runner `artifacts/codex/model-check.json` (if present; scaffold generation alone does not create it)

Additionally, it posts a PR comment summarizing model check and UI scaffold results.
