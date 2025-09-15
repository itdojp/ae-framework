# Natural Language → AE‑Spec → IR → Code Workflow (CodeX / Claude Code)

> 🌍 Language / 言語: English | 日本語

---

## 日本語（概要）

自然言語の要件を基に LLM で AE‑Spec を下書きし、ae‑framework の確定的なツールで `compile/validate/codegen` を行うエンドツーエンドの手順を示します（CodeX/Claude Code 両対応、外部 API キー不要）。

- Stdio ブリッジ: `pnpm run codex:spec:stdio`（アクション: compile/validate/codegen）
- MCP サーバ: `pnpm run codex:mcp:spec`（ツール: ae_spec_compile/validate/codegen）
- 反復: lenient validate → 修正 → strict compile → codegen

詳細なコマンドやプロンプトテンプレートは以下の英語セクションを参照してください。

This guide shows how to run an end‑to‑end workflow using your editor/agent’s own LLM for drafting AE‑Spec, while ae‑framework provides deterministic tools for compile/validate/codegen. Works with CodeX and Claude Code (no external API keys required on our side).

## Overview

- Authoring: Your LLM drafts and refines `spec/*.ae-spec.md` from natural‑language requirements.
- Validation: Call ae‑framework tools to compile + lint and get structured issues.
- Convergence: Iterate until strict validation passes (errors=0; warnings within policy).
- Generation: Compile → AE‑IR → code (TypeScript/API/DB/UI).

## Tools

- Stdio bridge (no MCP): `pnpm run codex:spec:stdio`
  - Actions (single‑line JSON): `compile`, `validate`, `codegen`
- MCP server (optional): `pnpm run codex:mcp:spec`
  - Tools: `ae_spec_compile`, `ae_spec_validate`, `ae_spec_codegen`

## CodeX Workflow Template (stdio)

1) Draft AE‑Spec from NL requirements (LLM step)
- Save to `spec/feature.ae-spec.md`.
- Keep sections: Glossary, Domain, Invariants, Use Cases, API, UI, NFR.
- Use field types: `string|number|boolean|date|uuid|email|url|json|array|object`.

2) Validate in lenient mode and collect issues
```bash
# Returns JSON { ok, data: { passed, summary, issues[...] } }
echo '{"action":"validate","args":{"inputPath":"spec/feature.ae-spec.md","relaxed":true,"maxWarnings":999}}' | pnpm run codex:spec:stdio
```
- Feed issues back to your LLM and ask for edits.

3) Repeat until strict pass
- When the lenient result shows errors=0 and warnings small, switch to strict compile:
```bash
# Strict compile → AE‑IR (.ae/ae-ir.json)
echo '{"action":"compile","args":{"inputPath":"spec/feature.ae-spec.md","outputPath":".ae/ae-ir.json","relaxed":false}}' | pnpm run codex:spec:stdio
```

4) Code generation
```bash
# Generate TS/API/DB artifacts from IR
echo '{"action":"codegen","args":{"irPath":".ae/ae-ir.json","targets":["typescript","api","database"]}}' | pnpm run codex:spec:stdio
```

5) Semi-automated iteration (convenience)
```bash
# Iteratively validate (lenient), emit revision prompts, and attempt strict compile+codegen
pnpm run codex:spec:iterate -- spec/feature.ae-spec.md 5 10
# Args: <spec> <maxIter=5> <maxWarnings=10>
```

6) Prompt joiner (for CodeX agents)
```bash
# Convert the last validate JSON into a concise revision instruction for your LLM
pnpm run codex:spec:prompt -- artifacts/spec-iterate/issues-01.json spec/feature.ae-spec.md > artifacts/spec-iterate/revise-01.md
# Feed revise-01.md to your agent; update the spec; press Enter in spec-iterate loop.
```

## Claude Code Workflow Template (MCP)

1) Register MCP server
```jsonc
{ "mcpServers": { "ae-framework-spec": { "name": "AE Framework Spec Tools", "command": "pnpm", "args": ["run", "codex:mcp:spec"], "env": {} } } }
```

2) Draft AE‑Spec (LLM step) → `spec/feature.ae-spec.md`.

3) Validate + refine (tool calls)
- `ae_spec_validate` with `{ inputPath, relaxed: true, maxWarnings: 999 }` → fix issues → repeat.

4) Strict compile + codegen
- `ae_spec_compile` with `{ inputPath, outputPath: ".ae/ae-ir.json", relaxed: false }`
- `ae_spec_codegen` with `{ irPath: ".ae/ae-ir.json", targets: ["typescript","api","database"] }`

## Prompt Template (for LLM drafting/refinement)

System:
- Convert natural‑language requirements to AE‑Spec Markdown with sections: Glossary, Domain (entities with typed fields and required flags), Invariants, Use Cases, API (list as "- METHOD /path - summary"), UI, NFR. Use field types from string|number|boolean|date|uuid|email|url|json|array|object. Fix prior validation issues and aim to pass strict validation.

User (first draft):
- Provide the raw requirements. Ask for a complete AE‑Spec draft.

User (iteration):
- Paste validator issues (JSON). Ask to address each issue, preserving prior valid content. If enum-like fields are used, map to supported base types (e.g., string). Ensure invariants reference existing entities. Ensure API paths start with "/".

## Tips

- Lenient mode speeds up early iterations; strict mode must pass before codegen is considered final.
- Keep entity names stable; use required fields for keys.
- Prefer short summaries for API; set path tokens as `{id}`.

## Artifacts
- Iterations: `artifacts/spec-synthesis/iter-*.md` (if using `spec synth`)
- Final: `spec/*.ae-spec.md`, `.ae/ae-ir.json`, `generated/*`
