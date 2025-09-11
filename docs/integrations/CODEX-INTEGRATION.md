# CodeX Integration Guide (PoC → MCP → Adapter)

This guide explains how to use ae-framework in the CodeX (agentic coding) environment. While Claude Code is the primary integration, CodeX can leverage ae-framework via CLI (PoC), MCP servers, or a future dedicated adapter.

## Overview

- Minimal: CLI bridge (PoC)
- Recommended: MCP integration (reuse existing MCP servers)
- Adapter: CodeX Task Adapter via stdio bridge (JSON-in/JSON-out)

## 1) CLI Bridge (PoC)

Run ae-framework commands from CodeX tasks. This requires file write permissions for artifacts.

### Quickstart

```bash
# Build first
pnpm run build

# Run PoC (verify; optional UI scaffold and formal generation)
pnpm run codex:quickstart

# Examples:
#   UI scaffold demo: CODEX_RUN_UI=1 pnpm run codex:quickstart
#   Formal + OpenAPI + contract templates: CODEX_RUN_FORMAL=1 pnpm run codex:quickstart
```

Artifacts (logs, summaries) will be written under `artifacts/`.

### Notes
- The quickstart finds the CLI at `dist/src/cli/index.js` (or `dist/cli.js` as fallback).
- Non-zero exit codes fail the step, enabling clear feedback in CodeX.
 - Build prerequisites: Node.js >= 20.11 (<23) and pnpm 10 (use Corepack: `corepack enable`).

### Minimal Phase 6 sample (for UI scaffold)

If you want to try UI scaffolding with a minimal domain, use:

```bash
cat samples/phase-state.example.json | jq .

# Run UI scaffold directly via CLI (outside CodeX adapter):
pnpm run build && node dist/src/cli/index.js ui-scaffold --components
```

## 2) MCP Integration (Recommended)

ae-framework ships MCP servers that can be used by CodeX as an MCP client.

### Available servers
- Intent: `src/mcp-server/intent-server.ts`
- Test generation: `src/mcp-server/test-generation-server.ts`
- Verify: `src/mcp-server/verify-server.ts`
- Code generation: `src/mcp-server/code-generation-server.ts`
- Spec Synthesis Utilities: `src/mcp-server/spec-synthesis-server.ts`

### Helper scripts

```bash
pnpm run codex:mcp:intent
pnpm run codex:mcp:test
pnpm run codex:mcp:verify
pnpm run codex:mcp:code
pnpm run codex:mcp:spec
```

### Client setup (example)
Configure CodeX to connect to the servers via stdio on Node 20.11+. Ensure the working directory is the ae-framework repo (or set `cwd`).

Sample configs are provided under `samples/`:

- JSON: `samples/codex-mcp-config.json`
- YAML: `samples/codex-mcp-config.yaml`

Replace `${AE_FRAMEWORK_ROOT}` with your local path. Minimal JSON example:

```json
{
  "mcpServers": {
    "ae-intent": {
      "command": "pnpm",
      "args": ["run", "codex:mcp:intent"],
      "cwd": "/path/to/ae-framework"
    },
    "ae-verify": {
      "command": "pnpm",
      "args": ["run", "codex:mcp:verify"],
      "cwd": "/path/to/ae-framework"
    }
  }
}
```

## 3) CodeX Task Adapter (Stdio Bridge)

A dedicated adapter maps CodeX TODO/Plan/Tool calls to ae-framework phases. Use the stdio bridge for simple JSON I/O.

### Current scope
- Phase handlers: intent, formal, stories, validation, modeling, ui
- Request/response contracts: `TaskRequest` / `TaskResponse`
- Artifacts: writes JSON summaries to `artifacts/codex/`

### Usage (stdio)
- Script: `pnpm run codex:adapter`
- Example:
```bash
echo '{"description":"Generate UI","subagent_type":"ui","context":{"phaseState":{"entities":{}}}}' | pnpm run codex:adapter
```

### Implementation notes
- File: `src/agents/codex-task-adapter.ts` (core), `scripts/codex/adapter-stdio.mjs` (bridge)
- UI: uses `UIScaffoldGenerator` when `context.phaseState.entities` is provided; otherwise dry-run
- Formal: `FormalAgent` generates TLA+ and OpenAPI (best-effort model checking)
- Validation: runtime schema validation (Zod) for `context.phaseState` blocks on invalid inputs with actionable messages.
 - Contract/E2E templates: when OpenAPI is available in quickstart, `scripts/codex/generate-contract-tests.mjs` scaffolds tests under `tests/api/generated/` and writes `artifacts/codex/openapi-contract-tests.json`.

## 4) CodeX (no MCP) – Spec Tools over stdio
- Script: `pnpm run codex:spec:stdio`
- Actions:
  - `compile`: `echo '{"action":"compile","args":{"inputPath":"spec/my.ae-spec.md","outputPath":".ae/ae-ir.json","relaxed":true}}' | pnpm run codex:spec:stdio`
  - `validate`: `echo '{"action":"validate","args":{"inputPath":"spec/my.ae-spec.md","relaxed":true,"maxWarnings":999}}' | pnpm run codex:spec:stdio`
  - `codegen`: `echo '{"action":"codegen","args":{"irPath":".ae/ae-ir.json","targets":["typescript","api","database"]}}' | pnpm run codex:spec:stdio`

Flow suggestion:
- CodeX LLM drafts AE‑Spec → call `validate` to get issues → revise → repeat → when stable, `compile` (strict) → `codegen`.
- この方法はMCP不要・外部APIキー不要で、CodeXのランタイムだけで完結します。

### Spec Synthesis via MCP (no external API keys)
- Start: `pnpm run codex:mcp:spec`
- Tools:
  - `ae_spec_compile`: compile AE-Spec to AE-IR (lenient or strict)
  - `ae_spec_validate`: validate with summary of issues (lenient/strict)
  - `ae_spec_codegen`: generate code from `.ae/ae-ir.json`
- Flow: CodeX uses its own LLM for drafting the AE‑Spec and calls these tools to compile/lint/codegen, iterating until strict validation passes.
 

## Operational Considerations

- Environment: Node >= 20.11 (<23), pnpm 10 (Corepack recommended: `corepack enable`).
- Artifacts: prefer JSON/Markdown outputs for CodeX UI consumption.
- Security: keep CLI/file permissions aligned with CodeX sandbox settings.
- E2E dependencies (Playwright/LHCI): optional; introduce in CI/local first.

### Environment variables
- `CODEX_ARTIFACTS_DIR`: override adapter artifact output dir (defaults to `./artifacts/codex`).
- `CODEX_RUN_UI`: `1` to enable Phase 6 UI scaffold in quickstart.
- `CODEX_PHASE_STATE_FILE`: path to phase state JSON for UI scaffold.
- `CODEX_UI_DRY_RUN`: `1` (default) to simulate, `0` to write files for UI scaffold.
- `CODEX_RUN_FORMAL`: `1` to enable formal generation in quickstart.
- `CODEX_FORMAL_REQ`: requirement text for formal/OpenAPI generation when `CODEX_RUN_FORMAL=1`.
- `CODEX_SKIP_QUALITY`: `1` to skip running quality gates in quickstart.
- `CODEX_TOLERANT`: `1` to force quickstart to exit 0 even if steps fail (non-blocking demo mode).

### Runtime Contracts (optional)
- Generate runtime contracts from a formal spec and inject them into OpenAPI-generated handlers.
- Use `CodeGenerationAgent.generateContractsSkeleton(formalSpec)` and pass `includeContracts: true` to `generateFromOpenAPI`.
- See `docs/verify/RUNTIME-CONTRACTS.md` and Quick Start for examples.
- CI integration and PR summary details are described in `docs/verify/FORMAL-CHECKS.md` and `docs/verify/TRACEABILITY-GUIDE.md`.

### OpenAPI Test Generator
- Script: `pnpm run codex:generate:tests [-- --use-operation-id] [--with-input]`
- Reads `artifacts/codex/openapi.(json|yaml)` (or `CONTRACTS_OPENAPI_PATH`).
- Generates minimal tests under `tests/api/generated/` using:
  - OperationId in file/test names when `--use-operation-id` is provided
  - Minimal sample input from requestBody schema when `--with-input` is provided

### Codegen Options (OpenAPI)
- `includeContracts`: injects runtime contracts (Zod + pre/post) into handlers
- `useOperationIdForFilenames`: prefer `operationId` for route filenames (fallback: path+method)
- `useOperationIdForTestNames` (generator): prefer `operationId` in test titles/filenames

## Acceptance Criteria (incremental)

1) PoC: CodeX can run `verify` (and optional `ui-scaffold`) via CLI and produce artifacts.
2) MCP: CodeX connects to intent/test/verify MCP servers and exchanges results.
3) Adapter (optional): Phases can be orchestrated from CodeX plans with clear progress and results.

## End-to-End Walkthrough (CLI/MCP)

1. Build the framework
```bash
pnpm run build
```

2. Run quick PoC from CodeX task (produces artifacts summary)
```bash
pnpm run codex:quickstart
# Or enable Phase 6 demo: CODEX_RUN_UI=1 pnpm run codex:quickstart
```

3. Start MCP servers and connect from CodeX (example)
```bash
pnpm run codex:mcp:intent &
pnpm run codex:mcp:verify &
# Configure CodeX MCP client to connect via stdio to the above
```

4. UI generation (Phase 6)
```bash
# Use minimal sample
cat samples/phase-state.example.json | jq .

# CLI scaffold
node dist/src/cli/index.js ui-scaffold --components
```

Quickstart with a custom phase-state (optional):

```bash
pnpm run build
CODEX_RUN_UI=1 CODEX_PHASE_STATE_FILE=samples/phase-state.example.json pnpm run codex:quickstart

# Dry-run is enabled by default; set CODEX_UI_DRY_RUN=0 to write files
```

Skip quality gates or run in tolerant mode (optional):
```bash
CODEX_SKIP_QUALITY=1 pnpm run codex:quickstart
# or
CODEX_TOLERANT=1 pnpm run codex:quickstart
```

## Machine-readable artifacts

When the CodeX adapter runs phases, it writes JSON summaries to `artifacts/codex/`:

- `result-intent.json`, `result-formal.json`, `result-stories.json`, etc.
- Each file contains `{ phase, response, ts }` for downstream tooling.

In CI (`pr-verify.yml`), these are uploaded as an artifact named `codex-json-artifacts`.

Additionally, when running the formal phase, the adapter derives an OpenAPI specification and writes it to:

- `artifacts/codex/openapi.yaml`

This file is also uploaded in CI as `codex-openapi` if present.

On Windows/WSL
- Prefer running MCP servers from WSL for consistent `cwd` and path behavior
- If using Windows paths, ensure `cwd` is an absolute path without spaces and that execution policy permits scripts
- Use Corepack (`corepack enable`) to manage pnpm versions consistently

See also: [CodeX Quick Start](./QUICK-START-CODEX.md) and [CodeX Artifacts and JSON Formats](./CODEX-ARTIFACTS.md) for detailed usage and data shapes.


Windows/WSL notes (quickstart formal/UI)
- Ensure `pnpm run build` is executed so that `dist/` exists (quickstart loads from `dist`)
- Prefer WSL for consistent `cwd` and path behavior; if using Windows paths, avoid spaces
- Use Corepack: `corepack enable` to manage pnpm; run the quickstart from repository root

One-liner examples:
- PowerShell:
```powershell
$env:CODEX_RUN_FORMAL="1"; pnpm run build; pnpm run codex:quickstart
```
- cmd.exe:
```bat
set CODEX_RUN_FORMAL=1 && pnpm run build && pnpm run codex:quickstart
```
