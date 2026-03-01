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
- The generator supports explicit directives in the formal-spec text:
  - `@input <type>` / `@output <type>` (`object|array|string|number|boolean|unknown`)
  - `@pre <expr>` / `@post <expr>`
  - `@state <A|B|C>` / `@transition <A -> B if condition>`
- Generated files expose `generationWarnings` so unsupported directives or missing structure are explicit.

### How to use (initial)

1) Provide a formal spec (TLA+/Alloy) as a string to `CodeGenerationAgent.generateContractsSkeleton(formalSpec)`.
2) The agent returns files under `src/contracts/` (paths + contents) you can write to disk.
3) Integrate contracts into your service endpoints or use them in tests for runtime checking.
4) When generating OpenAPI handlers, pass `includeContracts: true` to inject runtime validation stubs.

Minimal example (TypeScript):

```ts
type GeneratedFile = { path: string; content: string };

async function generateContractsSkeleton(formalSpec: string): Promise<GeneratedFile[]> {
  void formalSpec;
  return [{ path: 'src/contracts/sample.ts', content: '// generated' }];
}

async function generateFromOpenAPI(
  openapi: string,
  options: { framework: 'fastify'; includeValidation: boolean; includeContracts: boolean },
): Promise<{ files: GeneratedFile[] }> {
  void openapi;
  void options;
  return { files: [] };
}

async function main(): Promise<void> {
  // 1) Generate runtime contracts from a formal spec string
  const formalSpec = `---- MODULE Sample ----`; // TLA+ or Alloy snippet
  const contractFiles = await generateContractsSkeleton(formalSpec);
  for (const file of contractFiles) {
    console.log(`write: ${file.path}`);
  }

  // 2) Generate API code with contracts injected
  const openapi = '...'; // OpenAPI YAML/JSON string
  const generated = await generateFromOpenAPI(openapi, {
    framework: 'fastify',
    includeValidation: true,
    includeContracts: true,
  });
  console.log(generated.files.length);
}

void main();
```

Directive-oriented example:

```text
@input object
@output number
@pre input != null
@post output != null
@state Init|Validated|Done
@transition Init -> Validated if input != null
@transition Validated -> Done if output != null
```

> This is an initial skeleton; future versions will extract specific properties.

### Optional enforcement in CI

Set `CONTRACTS_ENFORCE=1` in the environment to make the `contracts-exec` step fail the PR when minimal parse/pre/post checks fail. Default is report-only.

Alternatively, add a PR label `enforce-contracts`. The verify workflow translates this label into `CONTRACTS_ENFORCE=1` automatically for that PR.

### Supplying sample input

Set `CONTRACTS_SAMPLE_INPUT=/path/to/input.json` to feed a JSON object as input to the runtime contracts execution. This helps validate schemas and pre/post on a realistic shape. When absent, `{}` is used.

Alternatively, set `CONTRACTS_OPENAPI_PATH` (defaults to `artifacts/codex/openapi.yaml` or `openapi.json`) and the runner will try to derive a simple sample. For JSON it prefers the first `components.schemas` object (by type) to synthesize an example; otherwise falls back to the first path; for YAML it extracts the first JSON block (best‑effort).
