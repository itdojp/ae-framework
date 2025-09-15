# CodeX Quick Start (ae-framework)

> 🌍 Language / 言語: English | 日本語

---

## 日本語（概要）

このガイドは CodeX から ae-framework を最短で使うための手順をまとめています（CLI/MCP）。

- 前提: Node 20.11+, pnpm 10（Corepack 推奨）、最初に `pnpm run build`
- 1) ワンコマンド PoC（Verify + Formal）: `CODEX_RUN_FORMAL=1 pnpm run codex:quickstart`
- 2) UI スキャフォールド（Phase 6）: `CODEX_RUN_UI=1 CODEX_PHASE_STATE_FILE=... pnpm run codex:quickstart`
- 3) MCP サーバ起動: `pnpm run codex:mcp:intent & pnpm run codex:mcp:verify &`
- 成果物: `artifacts/codex/` 配下（OpenAPI, TLA+, model-check, UI サマリ 等）

詳細は以下の英語セクションに記載のとおりです。

This guide shows the fastest way to use ae-framework from CodeX via CLI/MCP.

## Prerequisites
- Node.js 20.11+
- pnpm 10 (Corepack recommended: `corepack enable`)
- Build the repo first (`pnpm run build`) — stdio/quickstart scripts load `dist/`

## 1) One-command PoC (Verify + Formal)
To customize formal input, set `CODEX_FORMAL_REQ` to your requirement text (single line or escaped).
```bash
pnpm run build
CODEX_RUN_FORMAL=1 pnpm run codex:quickstart
```
Outputs under `artifacts/`:
- `artifacts/codex/formal.tla` (TLA+)
- `artifacts/codex/openapi.yaml` (OpenAPI)
- `artifacts/codex/model-check.json` (model checking)
- `artifacts/codex/result-formal.json` (per-phase JSON)
- If OpenAPI is present, contract/E2E templates are scaffolded under `tests/api/generated/` and summarized in `artifacts/codex/openapi-contract-tests.json`.

Optional flags for smoother local runs:
```bash
# Skip quality gates entirely
CODEX_SKIP_QUALITY=1 pnpm run codex:quickstart

# Tolerant mode: always exit 0 even if steps fail
CODEX_TOLERANT=1 pnpm run codex:quickstart
```

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
 - To change where artifacts are written, set `CODEX_ARTIFACTS_DIR` (adapter) or run quickstart from the repo root.

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
## 4) Stdio Adapter (direct Task Adapter)
Pipe a `TaskRequest` JSON to the stdio adapter and receive a `TaskResponse` JSON.
```bash
pnpm run build
echo '{"description":"Generate UI","subagent_type":"ui","context":{"phaseState":{"entities":{}}}}' | pnpm run codex:adapter
```

---

## 日本語

このガイドは、CodeX から ae-framework を最短で使う手順（CLI/MCP）をまとめたものです。

### 前提条件
- Node.js 20.11+
- pnpm 10（Corepack 推奨: `corepack enable`）
- まずビルド: `pnpm run build`（quickstart/stdio スクリプトは `dist/` を参照）

### 1) ワンコマンド PoC（Verify + Formal）
OpenAPI/TLA+ 等の成果物を `artifacts/` に出力します。必要なら `CODEX_FORMAL_REQ` で要件文字列を指定。
```bash
pnpm run build
CODEX_RUN_FORMAL=1 pnpm run codex:quickstart
```
主な出力:
- `artifacts/codex/formal.tla`（TLA+）
- `artifacts/codex/openapi.yaml`（OpenAPI）
- `artifacts/codex/model-check.json`（モデル検査）
- `artifacts/codex/result-formal.json`（各フェーズ要約）
- OpenAPI があれば `tests/api/generated/` にテンプレ生成＋`artifacts/codex/openapi-contract-tests.json`

便利オプション:
```bash
# 品質ゲートをスキップ
CODEX_SKIP_QUALITY=1 pnpm run codex:quickstart

# 寛容モード（失敗時でも exit 0）
CODEX_TOLERANT=1 pnpm run codex:quickstart
```

### 2) UI スキャフォールド（Phase 6）
同梱の Phase State サンプルを使って UI をスキャフォールド。
```bash
pnpm run build
CODEX_RUN_UI=1 \
CODEX_PHASE_STATE_FILE=samples/phase-state.example.json \
CODEX_UI_DRY_RUN=1 \
pnpm run codex:quickstart
```
- 既定は dry-run。ファイル出力する場合は `CODEX_UI_DRY_RUN=0`
- サマリ: `artifacts/codex/ui-summary.json`
- 出力ディレクトリ変更: `CODEX_ARTIFACTS_DIR`

### 3) MCP 統合
MCP サーバを起動し、CodeX から接続。
```bash
pnpm run codex:mcp:intent &
pnpm run codex:mcp:verify &
```
設定例:
- JSON: `samples/codex-mcp-config.json`
- YAML: `samples/codex-mcp-config.yaml`

### 4) Stdio アダプタ（直接 Task Adapter）
`TaskRequest` を標準入力に渡し、`TaskResponse` を受け取ります。
```bash
pnpm run build
echo '{"description":"Generate UI","subagent_type":"ui","context":{"phaseState":{"entities":{}}}}' | pnpm run codex:adapter
```

### Windows/WSL の注意
- 先に `pnpm run build` を実行して `dist/` を用意
- WSL 推奨。Windows パスは空白を避け、`cwd` は絶対パスで
- Corepack（`corepack enable`）で pnpm を管理
