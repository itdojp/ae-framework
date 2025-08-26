# CodeX Quick Start (ae-framework)

This guide shows the fastest way to use ae-framework from CodeX via CLI/MCP.

## Prerequisites
- Node.js 20.11+
- pnpm 9 (Corepack: `corepack enable`)
- Repository built (`pnpm run build`)

## 1) One-command PoC (Verify + Formal)
```bash
pnpm run build
CODEX_RUN_FORMAL=1 pnpm run codex:quickstart
```
Outputs under `artifacts/`:
- `artifacts/codex/formal.tla` (TLA+)
- `artifacts/codex/openapi.yaml` (OpenAPI)
- `artifacts/codex/model-check.json` (model checking)
- `artifacts/codex/result-formal.json` (per-phase JSON)

## 2) UI Scaffold (Phase 6)
Use the included sample Phase State:
```bash
pnpm run build
CODEX_RUN_UI=1 \
CODEX_PHASE_STATE_FILE=samples/phase-state.example.json \
CODEX_UI_DRY_RUN=1 \
pnpm run codex:quickstart
```
- Dry-run by default. Set `CODEX_UI_DRY_RUN=0` to write files.
- UI summary is saved as `artifacts/codex/ui-summary.json`.

## 3) MCP Integration
Start MCP servers and connect from CodeX:
```bash
pnpm run codex:mcp:intent &
pnpm run codex:mcp:verify &
```
Sample configs:
- JSON: `samples/codex-mcp-config.json`
- YAML: `samples/codex-mcp-config.yaml`

## Artifacts & Schemas
- Overview: `docs/integrations/CODEX-ARTIFACTS.md`
- Schemas: `docs/integrations/schemas/*`
- Examples: `docs/integrations/examples/*`

## Windows/WSL Tips
- Build first so `dist/` exists.
- Prefer WSL for consistent paths; avoid spaces in Windows paths.
- PowerShell:
```powershell
$env:CODEX_RUN_FORMAL="1"; pnpm run build; pnpm run codex:quickstart
```
- cmd.exe:
```bat
set CODEX_RUN_FORMAL=1 && pnpm run build && pnpm run codex:quickstart
```
