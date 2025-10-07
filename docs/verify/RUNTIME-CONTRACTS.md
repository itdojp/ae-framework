## Runtime Contracts from Formal Specs (Week 3)

> 🌍 Language / 言語: English | 日本語

---

## 日本語（概要）

形式仕様から実行時契約（Zod スキーマ、事前/事後条件）やステートマシンの雛形を生成し、任意で CI のゲートに組み込む手順を説明します。

- `CodeGenerationAgent.generateContractsSkeleton(formalSpec)` で契約を生成し、`src/contracts/` に出力
- OpenAPI 生成時に `includeContracts: true` で契約を注入
- CI での任意ゲート: `CONTRACTS_ENFORCE=1` または PR ラベル `enforce-contracts`
- サンプル入力: `CONTRACTS_SAMPLE_INPUT` または `CONTRACTS_OPENAPI_PATH` を指定

詳細は下の英語セクションのコード例・オプション一覧を参照してください。

This document outlines an opt-in path to generate runtime contracts (e.g., Zod schemas, pre/post conditions) and state-machine shells from formal specs.

### Overview

- Contracts are generated alongside code and can be enabled per feature.
- Contracts validate inputs/outputs and pre/post conditions in runtime and can be wired into `verify` as an optional gate.

### How to use (initial)

1) Provide a formal spec (TLA+/Alloy) as a string to `CodeGenerationAgent.generateContractsSkeleton(formalSpec)`.
2) The agent returns files under `src/contracts/` (paths + contents) you can write to disk.
3) Integrate contracts into your service endpoints or use them in tests for runtime checking.
4) When generating OpenAPI handlers, pass `includeContracts: true` to inject runtime validation stubs.

Minimal example (TypeScript):

```ts
import { CodeGenerationAgent } from '@/agents/code-generation-agent';
import { promises as fs } from 'fs';

const agent = new CodeGenerationAgent();

// 1) Generate runtime contracts from a formal spec string
const formalSpec = `---- MODULE Sample ----`; // TLA+ or Alloy snippet
const contractFiles = await agent.generateContractsSkeleton(formalSpec);
for (const f of contractFiles) {
  await fs.mkdir(require('path').dirname(f.path), { recursive: true });
  await fs.writeFile(f.path, f.content);
}

// 2) Generate API code with contracts injected
const openapi = '...'; // OpenAPI YAML/JSON string
const generated = await agent.generateFromOpenAPI(openapi, {
  framework: 'fastify',
  includeValidation: true,
  includeContracts: true,
});
// write generated.files ...
```

> This is an initial skeleton; future versions will extract specific properties.

### Optional enforcement in CI

Set `CONTRACTS_ENFORCE=1` in the environment to make the `contracts-exec` step fail the PR when minimal parse/pre/post checks fail. Default is report-only.

Alternatively, add a PR label `enforce-contracts`. The verify workflow translates this label into `CONTRACTS_ENFORCE=1` automatically for that PR.

### Supplying sample input

Set `CONTRACTS_SAMPLE_INPUT=/path/to/input.json` to feed a JSON object as input to the runtime contracts execution. This helps validate schemas and pre/post on a realistic shape. When absent, `{}` is used.

Alternatively, set `CONTRACTS_OPENAPI_PATH` (defaults to `artifacts/codex/openapi.yaml` or `openapi.json`) and the runner will try to derive a simple sample. For JSON it prefers the first `components.schemas` object (by type) to synthesize an example; otherwise falls back to the first path; for YAML it extracts the first JSON block (best‑effort).

### Running the report locally

The lightweight report runner lives at `scripts/verify/execute-contracts.ts`. Execute it with `pnpm tsx` so TypeScript modules are resolved without a build:

```bash
pnpm tsx scripts/verify/execute-contracts.ts
```

The script emits structured warnings instead of hard failures when optional inputs (OpenAPI artifacts, sample JSON) are missing, and always writes the summary to `artifacts/contracts/contracts-exec.json`. In report-only mode (`CONTRACTS_ENFORCE` 未設定), errors are captured in `results.error`; enforce mode (`CONTRACTS_ENFORCE=1`) will cause the workflow to fail if any parse/pre/post check is unsuccessful.
