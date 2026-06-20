---
docRole: derived
canonicalSource:
  - README.md
  - docs/agents/commands.md
lastVerified: '2026-03-10'
---

# Codex Integration Guide (PoC → MCP → Adapter)

> 🌍 Language / 言語: English | 日本語

---


This guide explains how to use ae-framework in the Codex (agentic coding) environment. Codex is a producer; ae-framework remains the agent-neutral assurance control plane that normalizes producer output into evidence, policy, and review artifacts. For GitHub Issue driven work, start with `docs/integrations/CODEX-ISSUE-RUNBOOK.md`.

## Overview

- Minimal: CLI bridge (PoC)
- Recommended: MCP integration (reuse existing MCP servers)
- Adapter: Codex Task Adapter via stdio bridge (JSON-in/JSON-out)

## 1) CLI Bridge (PoC)

Run ae-framework commands from Codex tasks. This requires file write permissions for artifacts.

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
- Non-zero exit codes fail the step, enabling clear feedback in Codex.
 - Build prerequisites: Node.js >= 20.11 (<23) and pnpm 10 (use Corepack: `corepack enable`).

### Minimal Phase 6 sample (for UI scaffold)

If you want to try UI scaffolding with a minimal domain, use:

```bash
cat samples/phase-state.example.json | jq .

# Preview UI scaffold directly via CLI (outside Codex adapter; dry-run by default):
pnpm run build && node dist/src/cli/index.js ui-scaffold --components --dry-run

# Materialize only from a trusted workspace/ref after explicit approval:
node dist/src/cli/index.js ui-scaffold --components --apply --approval-scope high-impact:codegen-materialize
```

## 2) MCP Integration (Recommended)

ae-framework ships MCP servers that can be used by Codex as an MCP client.

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

### Agent / MCP boundary smoke test

Use the focused smoke lane when changing agent entrypoints, MCP stdio servers, or provider fallback behavior:

```bash
pnpm run test:agents:smoke
```

This lane starts the Intent MCP server over stdio, verifies the client initialize handshake, lists tools, performs a basic tool call, and confirms that missing external provider API keys fall back to the local echo provider without network access.

### Agent / MCP 境界 smoke test

agent entrypoint、MCP stdio server、provider fallback を変更した場合は、次の focused smoke lane を使います。

```bash
pnpm run test:agents:smoke
```

この lane は Intent MCP server を stdio で起動し、client initialize handshake、tool list、basic tool call、外部 provider API key 未設定時の local echo provider fallback を確認します。

### Client setup (example)
Configure Codex to connect to the servers via stdio on Node 20.11+. Ensure the working directory is the ae-framework repo (or set `cwd`).

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

## 3) Codex Task Adapter (Stdio Bridge)

A dedicated adapter maps Codex TODO/Plan/Tool calls to ae-framework phases. Use the stdio bridge for simple JSON I/O.

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
- Continuation contract (No Human Bottleneck): `docs/integrations/CODEX-CONTINUATION-CONTRACT.md`
- Operational recipe (copy/paste runbook): `docs/agents/recipes/continuous-loop.md`

### TaskResponse schema transition note (Contract v1)

- `schema/codex-task-response.schema.json` now enforces:
  - `shouldBlockProgress=false` => `nextActions` must be non-empty
  - `shouldBlockProgress=true` => `nextActions` and `warnings` must be non-empty
  - `nextActions`/`warnings` item strings must be non-empty
- Migration recommendation:
  - Move blocked responses to explicit `blockingReason` / `requiredHumanInput` fields where possible.
  - Existing blocked responses without those fields are accepted for compatibility.
  - Local schema sanity check: `pnpm run check:schemas`
  - Adapter normalization tests: `pnpm vitest run tests/unit/agents/codex-task-adapter.test.ts tests/unit/scripts/codex-adapter-stdio.test.ts`

## 4) Codex (no MCP) – Spec Tools over stdio
- Script: `pnpm run codex:spec:stdio`
- Actions:
  - `validate`: `echo '{"action":"validate","args":{"inputPath":"spec/my.ae-spec.md","relaxed":true,"maxWarnings":999}}' | pnpm run codex:spec:stdio`
  - `compile`: `printf '%s\n' '{"action":"compile","approval":{"approved":true,"scope":"codex-spec-stdio"},"args":{"inputPath":"spec/my.ae-spec.md","outputPath":"artifacts/spec-synthesis/ae-ir.json","relaxed":true}}' | AE_CODEX_SPEC_STDIO_TRUSTED_APPROVAL=1 pnpm run codex:spec:stdio`
  - `codegen`: `printf '%s\n' '{"action":"codegen","approval":{"approved":true,"scope":"codex-spec-stdio-codegen"},"args":{"irPath":"artifacts/spec-synthesis/ae-ir.json","targets":["typescript","api","database"]}}' | AE_CODEX_SPEC_STDIO_TRUSTED_APPROVAL=1 pnpm run codex:spec:stdio`
- Path and approval policy:
  - Caller-supplied paths must be workspace-relative POSIX paths; absolute paths, `..` / `.` segments, backslashes, and `.git` targets are rejected.
  - AE-IR and generated-code writes are constrained to `artifacts/spec-synthesis` by default.
  - `compile` with `outputPath`, `codegen`, and cold-checkout spec-compiler auto-build require trusted approval (`AE_CODEX_SPEC_STDIO_TRUSTED_CONTEXT=1`, or `AE_CODEX_SPEC_STDIO_TRUSTED_APPROVAL=1` plus `approval.approved=true`; codegen should use `codex-spec-stdio-codegen` or an accepted umbrella scope).
  - `codegen` materialization is delegated to `codegen generate --apply --approval-scope high-impact:codegen-materialize`; untrusted workspaces/refs remain dry-run at the child CLI boundary.

Flow suggestion:
- Codex LLM drafts AE‑Spec → call `validate` to get issues → revise → repeat → when stable, `compile` (strict) → `codegen`.
- この方法はMCP不要・外部APIキー不要で、Codexのランタイムだけで完結します。

### Spec Synthesis via MCP (no external API keys)
- Start: `pnpm run codex:mcp:spec`
- Tools:
  - `ae_spec_compile`: compile AE-Spec to AE-IR (lenient or strict)
  - `ae_spec_validate`: validate with summary of issues (lenient/strict)
  - `ae_spec_codegen`: generate code from `.ae/ae-ir.json` with `approvalScope: "high-impact:codegen-materialize"` for materialization
- Flow: Codex uses its own LLM for drafting the AE‑Spec and calls these tools to compile/lint/codegen, iterating until strict validation passes.
 

## GitHub Issue driven Codex work

Use `docs/integrations/CODEX-ISSUE-RUNBOOK.md` when a GitHub Issue is the task input. It includes copy/paste `gh issue view` extraction, non-interactive `codex exec`, interactive `codex --cd`, pre-work/post-work checklists, and subagent/worktree safety boundaries.

Use `docs/agents/agent-producer-matrix.md` to decide whether Codex CLI output should become `change-package/v2`, `ae-handoff/v1`, `hook-feedback/v1`, `claim-evidence-manifest/v1`, or another judgment artifact.

Use `docs/agents/evidence-adapters.md` when Codex CLI output must be normalized from raw task summaries, command logs, or PR evidence into existing ae-framework artifacts without treating the Codex conclusion as a control-plane judgment.

### Context Pack preflight for Codex
Before asking Codex to edit code, treat Context Pack as the design SSOT rather than as a code-generation prompt. Use this reference order:

1. GitHub Issue body.
2. `AGENTS.md`.
3. `docs/spec/context-pack.md` and `spec/context-pack/boundary-map.json`.
4. Relevant acceptance tests, existing tests, and validation commands.

If the requested change conflicts with Context Pack constraints or the boundary map, stop before implementation and record `Context Pack conflict: found` with the conflicting IDs/paths in the PR or Issue comment. If no conflict is found, record `Context Pack conflict: none` in the PR body. Run the real package scripts after the change: `pnpm -s run context-pack:validate`, `pnpm -s run context-pack:verify-boundary-map`, and `pnpm -s run context-pack:deps` when dependency or slice assumptions changed. Use heavier Context Pack checks only when the Issue, touched fixture/schema, risk label, assurance profile, or critical-core boundary requires them.

```text
Before changing code, read the Context Pack, boundary map, and acceptance tests relevant to the Issue target files. Treat them as the design SSOT. If the requested change conflicts with Context Pack constraints, stop before implementation and report `Context Pack conflict: found`; otherwise record `Context Pack conflict: none` in the PR body. Do not add MBT, property, or formal lanes for routine changes unless the Issue, risk label, assurance profile, or critical-core boundary requires them.
```

```text
コードを変更する前に、Issue target files に関係する Context Pack、boundary map、acceptance tests を読んでください。これらを design SSOT として扱います。依頼内容が Context Pack の制約と矛盾する場合は、実装前に停止して `Context Pack conflict: found` を報告し、矛盾がない場合は PR body に `Context Pack conflict: none` を記録してください。Issue、risk label、assurance profile、critical-core boundary が要求しない限り、通常変更に MBT / property / formal lane を追加しないでください。
```

## Operational Considerations

- Environment: Node >= 20.11 (<23), pnpm 10 (Corepack recommended: `corepack enable`).
- Artifacts: prefer JSON/Markdown outputs for Codex UI consumption.
- Security: keep CLI/file permissions aligned with Codex sandbox settings.
- E2E dependencies (Playwright/LHCI): optional; introduce in CI/local first.
- Continuous execution runbook: `docs/agents/recipes/continuous-loop.md`

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
- Script: `pnpm run codex:generate:tests [-- --use-operation-id] [--with-input] [--output-dir <dir>]`
- Reads `artifacts/codex/openapi.(json|yaml)` (or `CONTRACTS_OPENAPI_PATH`).
- Generates minimal tests under `artifacts/codex/generated-tests/` by default so generated executable tests are review artifacts before they enter the active test tree.
- Writing directly under `tests/` requires both `--approve-generated-tests` and `CODEX_GENERATE_TESTS_APPROVAL=reviewed-generated-tests`.
- Uses:
  - OperationId in file/test names when `--use-operation-id` is provided
  - Minimal sample input from requestBody schema when `--with-input` is provided

### Codegen Options (OpenAPI)
- `includeContracts`: injects runtime contracts (Zod + pre/post) into handlers
- `useOperationIdForFilenames`: prefer `operationId` for route filenames (fallback: path+method)
- `useOperationIdForTestNames` (generator): prefer `operationId` in test titles/filenames
## Acceptance Criteria (incremental)

1) PoC: Codex can run `verify` (and optional `ui-scaffold`) via CLI and produce artifacts.
2) MCP: Codex connects to intent/test/verify MCP servers and exchanges results.
3) Adapter (optional): ae-framework phases can be coordinated from Codex task plans with clear progress and results; Codex remains the producer and ae-framework remains the assurance control plane.

## End-to-End Walkthrough (CLI/MCP)

1. Build the framework
```bash
pnpm run build
```

2. Run quick PoC from Codex task (produces artifacts summary)
```bash
pnpm run codex:quickstart
# Or enable Phase 6 demo: CODEX_RUN_UI=1 pnpm run codex:quickstart
```

3. Start MCP servers and connect from Codex (example)
```bash
pnpm run codex:mcp:intent &
pnpm run codex:mcp:verify &
# Configure Codex MCP client to connect via stdio to the above
```

4. UI generation (Phase 6)
```bash
# Use minimal sample
cat samples/phase-state.example.json | jq .

# CLI scaffold preview
node dist/src/cli/index.js ui-scaffold --components --dry-run

# Approved materialization
node dist/src/cli/index.js ui-scaffold --components --apply --approval-scope high-impact:codegen-materialize
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

When the Codex adapter runs phases, it writes JSON summaries to `artifacts/codex/`:

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

See also: [Codex Quick Start](./QUICK-START-CODEX.md), [Codex Artifacts and JSON Formats](./CODEX-ARTIFACTS.md), and [Codex Security Assurance Audit Runbook](./CODEX-SECURITY-AUDIT.md) for detailed usage, data shapes, and Security Assurance Lane operation.


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

---

## 日本語（概要）

このドキュメントは、Codex 環境で ae-framework を利用するための方法をまとめたものです。Claude Code が主統合ですが、Codex でも以下の 3 方式で利用できます。

- CLI ブリッジ（PoC）: `pnpm run codex:quickstart` などで CLI を直接呼び出し、`artifacts/` に成果を保存
- MCP 統合（推奨）: `pnpm run codex:mcp:intent` / `pnpm run codex:mcp:test` / `pnpm run codex:mcp:verify` / `pnpm run codex:mcp:code` / `pnpm run codex:mcp:spec` で MCP サーバを起動し、Codex クライアントから stdio で接続
- タスクアダプター（stdio）: TODO/Plan/Tool を ae-framework の各フェーズ（intent/formal/stories/validation/modeling/ui）へマッピング

運用上の注意（抜粋）
- 必要環境: Node >= 20.11 (<23), pnpm 10（Corepack 推奨）
- アーティファクトは `artifacts/codex/` 配下に JSON として出力（OpenAPI は `openapi.yaml`）
- Windows/WSL では WSL 推奨。Corepack（`corepack enable`）で pnpm を管理

詳細は英語セクション（上部）および以下の関連資料を参照してください。
- Codex Quick Start（クイックスタート）
- Codex Artifacts and JSON Formats（成果物の形式）
- Codex Continuation Contract（継続実行ルール）
- Codex Security Assurance Audit Runbook（Security Assurance Lane の運用手順）

## 日本語（詳細）

### 1) CLI ブリッジ（PoC）
- `pnpm run codex:quickstart` で verify/（任意で ui-scaffold/formal）を実行し、`artifacts/` 配下に成果物を保存
- 前提: Node 20.11+ / pnpm 10（Corepack 推奨）、`pnpm run build` 済（`dist/` を参照）
- 代表的な成果物: `artifacts/codex/result-*.json`, `openapi.yaml`, `formal.tla`, `model-check.json`

### 2) MCP 統合（推奨）
- Intent/Test/Verify/Code/Spec の MCP サーバを同梱
- Codex から stdio で接続（`samples/codex-mcp-config.{json,yaml}` 参照）
- 使い分け: 企画・検証フローを Codex 側 LLM でドラフト→ MCP ツールで確定的処理

### 3) Codex タスクアダプター（stdio ブリッジ）
- TODO/Plan/Tool ↔ ae-framework の各フェーズをマッピング
- UI: `context.phaseState.entities` があれば `UIScaffoldGenerator` を実行
- Formal: OpenAPI/TLA+ を生成し、可能ならモデル検査まで
- 検証: 入力を Zod でバリデーションし、無効時は行動可能なエラー

### 4) MCP なしの stdio ツール（Spec）
- `codex:spec:stdio` の `compile/validate/codegen` アクションで AE-Spec をコンパイル/検証/コード生成
- Codex の LLM で下書き→ lenient validate で指摘収集→ strict compile→ codegen の反復
- 書き込み系アクションは既定で `artifacts/spec-synthesis` 配下に限定され、trusted approval が必要

### 運用上の考慮
- 環境: Node >= 20.11 (<23), pnpm 10（Corepack 推奨）
- 成果物: JSON/Markdown を優先（Codex UI で消費しやすい）
- セキュリティ: Codex のサンドボックスに合わせた権限設計
- E2E 依存（Playwright/LHCI）は任意（CI/ローカルから導入）

### 環境変数（主なもの）
- `CODEX_ARTIFACTS_DIR`, `CODEX_RUN_UI`, `CODEX_PHASE_STATE_FILE`, `CODEX_UI_DRY_RUN`
- `CODEX_RUN_FORMAL`, `CODEX_FORMAL_REQ`, `CODEX_SKIP_QUALITY`, `CODEX_TOLERANT`

### 実行時契約（任意）
- 形式仕様からランタイム契約を生成し、OpenAPI 生成ハンドラに注入（`includeContracts: true`）
- `docs/verify/RUNTIME-CONTRACTS.md` 参照

### OpenAPI テストジェネレーター
- `pnpm run codex:generate:tests` で `artifacts/codex/generated-tests/` にレビュー用の最小テンプレートを生成
- `tests/` 配下へ直接書く場合は `--output-dir tests/api/generated --approve-generated-tests` と `CODEX_GENERATE_TESTS_APPROVAL=reviewed-generated-tests` を併用
- `--use-operation-id` / `--with-input` で命名/最小入力を調整

### Codegen オプション（OpenAPI）
- `includeContracts` / `useOperationIdForFilenames` / `useOperationIdForTestNames`

### Codex向けContext Pack事前確認
Codexにコード編集を依頼する前に、Context Packをcode generation promptではなくdesign SSOTとして扱います。参照順は次です。

1. GitHub Issue本文。
2. `AGENTS.md`。
3. `docs/spec/context-pack.md` と `spec/context-pack/boundary-map.json`。
4. 関連する acceptance tests、既存テスト、validation command。

依頼内容が Context Pack constraints または boundary map と矛盾する場合は、実装前に停止し、PR または Issue comment に `Context Pack conflict: found` と矛盾する ID / path を記録します。矛盾がない場合は PR body に `Context Pack conflict: none` を記録します。変更後は実在するpackage scriptである `pnpm -s run context-pack:validate`、`pnpm -s run context-pack:verify-boundary-map`、依存やslice前提を変えた場合は `pnpm -s run context-pack:deps` を実行します。Issue、fixture/schema、risk label、assurance profile、critical-core boundary が要求する場合だけ、より重いContext Pack検証へ昇格します。

```text
Before changing code, read the Context Pack, boundary map, and acceptance tests relevant to the Issue target files. Treat them as the design SSOT. If the requested change conflicts with Context Pack constraints, stop before implementation and report `Context Pack conflict: found`; otherwise record `Context Pack conflict: none` in the PR body. Do not add MBT, property, or formal lanes for routine changes unless the Issue, risk label, assurance profile, or critical-core boundary requires them.
```

```text
コードを変更する前に、Issue target files に関係する Context Pack、boundary map、acceptance tests を読んでください。これらを design SSOT として扱います。依頼内容が Context Pack の制約と矛盾する場合は、実装前に停止して `Context Pack conflict: found` を報告し、矛盾がない場合は PR body に `Context Pack conflict: none` を記録してください。Issue、risk label、assurance profile、critical-core boundary が要求しない限り、通常変更に MBT / property / formal lane を追加しないでください。
```

### 受け入れ基準（漸進）
1) PoC 成果物が生成される（任意で UI）
2) MCP で intent/test/verify が往復可能
3) アダプターでプラン駆動のオーケストレーションが可能

### E2E 手順（CLI/MCP 要約）
1. `pnpm run build`
2. `pnpm run codex:quickstart`（UI は `CODEX_RUN_UI=1`。materialize する場合のみ `CODEX_UI_APPLY=1 CODEX_UI_APPROVAL_SCOPE=high-impact:codegen-materialize`）
3. `pnpm run codex:mcp:intent & pnpm run codex:mcp:verify &` に接続
4. preview: `node dist/src/cli/index.js ui-scaffold --components --dry-run`; materialize: `node dist/src/cli/index.js ui-scaffold --components --apply --approval-scope high-impact:codegen-materialize`

### 機械可読アーティファクト
- `artifacts/codex/result-*.json`, `openapi.yaml`, `model-check.json`（有無に応じて）
- CI では `codex-json-artifacts`, `codex-openapi` などとしてアップロード

### Windows/WSL
- 先に `pnpm run build` を実行（`dist/` 必須）
- WSL 推奨。Windows パスは空白回避、`cwd` は絶対パス
- Corepack で pnpm を管理
