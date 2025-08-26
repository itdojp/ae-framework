# CodeX Integration Guide (PoC → MCP → Adapter)

This guide explains how to use ae-framework in the CodeX (agentic coding) environment. While Claude Code is the primary integration, CodeX can leverage ae-framework via CLI (PoC), MCP servers, or a future dedicated adapter.

## Overview

- Minimal: CLI bridge (PoC)
- Recommended: MCP integration (reuse existing MCP servers)
- Advanced: CodeX-specific task adapter (future work)

## 1) CLI Bridge (PoC)

Run ae-framework commands from CodeX tasks. This requires file write permissions for artifacts.

### Quickstart

```bash
# Build first
pnpm run build

# Run PoC (verify, optionally UI scaffold with CODEX_RUN_UI=1)
pnpm run codex:quickstart

# Or: CODEX_RUN_UI=1 pnpm run codex:quickstart
```

Artifacts (logs, summaries) will be written under `artifacts/`.

### Notes
- The quickstart finds the CLI at `dist/src/cli/index.js` (or `dist/cli.js` as fallback).
- Non-zero exit codes fail the step, enabling clear feedback in CodeX.

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

### Helper scripts

```bash
pnpm run codex:mcp:intent
pnpm run codex:mcp:test
pnpm run codex:mcp:verify
pnpm run codex:mcp:code
```

### Client setup (example)
Configure CodeX to connect to the servers via stdio on Node 20.11+. Ensure the working directory is the ae-framework repo (or set `cwd`). Example (pseudoconfig):

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

## 3) CodeX Task Adapter (Future)

Design a dedicated adapter that maps CodeX TODO/Plan/Tool calls to ae-framework phases.

### Planned scope
- Phase handlers: intent, formal, stories, validation, modeling, ui
- Request/response contracts: reuse `src/agents/*-task-adapter.ts` patterns
- Telemetry integration: reuse phase6 OpenTelemetry metrics

### Current skeleton and behavior
- File: `src/agents/codex-task-adapter.ts`
- Phase routing: intent/stories/validation/modeling → delegates to existing adapters
- Formal: delegates to `FormalAgent` (`tla+` generation + validation summary)
- UI: uses `UIScaffoldGenerator` if `context.phaseState.entities` is provided; otherwise returns recommendations

## Operational Considerations

- Environment: Node 20.11+, pnpm 9 (Corepack).
- Artifacts: prefer JSON/Markdown outputs for CodeX UI consumption.
- Security: keep CLI/file permissions aligned with CodeX sandbox settings.
- E2E dependencies (Playwright/LHCI): optional; introduce in CI/local first.

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
