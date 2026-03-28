---
docRole: narrative
lastVerified: '2026-03-28'
---
## Runtime Contracts from Formal Specs (Week 3)

> 🌍 Language / 言語: English | 日本語

---

## English

This document outlines an opt-in path to generate runtime contracts (for example, Zod schemas, pre/post conditions, and state-machine shells) from formal specs and wire them into runtime verification or CI gates.

### Overview

- Generate contracts from a formal spec string via `CodeGenerationAgent.generateContractsSkeleton(formalSpec)` and write the returned files under `src/contracts/`.
- When generating OpenAPI-backed handlers, pass `includeContracts: true` so the generated code includes runtime validation stubs.
- CI enforcement stays opt-in. Use `CONTRACTS_ENFORCE=1` or the PR label `enforce-contracts` when you want failures to block the PR.
- Sample input for contract execution can come from `CONTRACTS_SAMPLE_INPUT` or be derived best-effort from `CONTRACTS_OPENAPI_PATH`.

### How to use (initial)

1. Provide a formal spec (TLA+ or Alloy) as a string to `CodeGenerationAgent.generateContractsSkeleton(formalSpec)`.
2. The agent returns generated files (`path` + `content`) for `src/contracts/`.
3. Integrate those contracts into runtime endpoints or tests.
4. If you also generate OpenAPI handlers, pass `includeContracts: true` to inject runtime validation stubs.

Minimal example (TypeScript):

```text
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
  const formalSpec = `---- MODULE Sample ----`; // TLA+ or Alloy snippet
  const contractFiles = await generateContractsSkeleton(formalSpec);
  for (const file of contractFiles) {
    console.log(`write: ${file.path}`);
  }

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

### Directive-oriented example

The generator supports explicit directives in the formal-spec text:

- `@input <type>` / `@output <type>` (`object|array|string|number|boolean|unknown`)
- `@pre <expr>` / `@post <expr>`
- `@state <A|B|C>` / `@transition <A -> B if condition>`

Example:

```text
@input object
@output number
@pre input != null
@post output != null
@state Init|Validated|Done
@transition Init -> Validated if input != null
@transition Validated -> Done if output != null
```

> This is an initial skeleton. Future versions may extract concrete field-level structure.

### Optional enforcement in CI

Set `CONTRACTS_ENFORCE=1` in the environment to make the `contracts-exec` step fail the PR when minimal input/output parse and pre/post checks fail. The default remains report-only.

Alternatively, add a PR label `enforce-contracts`. The verify workflow translates that label into `CONTRACTS_ENFORCE=1` automatically for that PR.

### Supplying sample input

Set `CONTRACTS_SAMPLE_INPUT=/path/to/input.json` to feed a JSON object into runtime contract execution. This helps validate schemas and pre/post conditions against a realistic shape. When it is absent, `{}` is used.

Alternatively, set `CONTRACTS_OPENAPI_PATH` (defaults to `artifacts/codex/openapi.yaml` or `openapi.json`). The runner then attempts a best-effort sample derivation from the OpenAPI document (JSON or YAML) in this order:

- it first tries to synthesize input from `requestBody.content['application/json'].schema` on the first operation;
- if that is not available, it falls back to the first entry in `components.schemas`;
- if neither is present, it finally falls back to using the first path key as a placeholder input shape.

### Operational notes

- Generated files expose `generationWarnings` so unsupported directives or missing structure stay explicit.
- `enforce-contracts` only affects the runtime-contracts lane. It does not enable unrelated formal checks.
- Use opt-in enforcement only on PRs where contract failures should block merge.

## 日本語

この文書では、形式仕様から実行時契約（たとえば Zod スキーマ、事前/事後条件、ステートマシン雛形）を生成し、実行時検証や CI ゲートへ組み込むための opt-in 運用を整理します。

### 概要

- `CodeGenerationAgent.generateContractsSkeleton(formalSpec)` に形式仕様文字列を渡すと、`src/contracts/` 向けの契約ファイルを生成できます。
- OpenAPI ベースのハンドラ生成では、`includeContracts: true` を指定すると runtime validation stub を埋め込めます。
- CI enforcement は既定で report-only です。PR を block したい場合だけ `CONTRACTS_ENFORCE=1` または PR ラベル `enforce-contracts` を使います。
- 契約実行用のサンプル入力は `CONTRACTS_SAMPLE_INPUT` で直接渡すか、`CONTRACTS_OPENAPI_PATH` から best-effort で導出します。

### 初期導入手順

1. TLA+ または Alloy の形式仕様文字列を `CodeGenerationAgent.generateContractsSkeleton(formalSpec)` に渡します。
2. 返り値として `src/contracts/` に書き込む生成ファイル（`path` と `content`）を受け取ります。
3. 生成した契約を runtime endpoint やテストに組み込みます。
4. OpenAPI ハンドラも同時生成する場合は、`includeContracts: true` を指定して runtime validation stub を注入します。

最小例（TypeScript）:

```text
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
  const formalSpec = `---- MODULE Sample ----`; // TLA+ または Alloy の断片
  const contractFiles = await generateContractsSkeleton(formalSpec);
  for (const file of contractFiles) {
    console.log(`write: ${file.path}`);
  }

  const openapi = '...'; // OpenAPI YAML/JSON 文字列
  const generated = await generateFromOpenAPI(openapi, {
    framework: 'fastify',
    includeValidation: true,
    includeContracts: true,
  });
  console.log(generated.files.length);
}

void main();
```

### ディレクティブ例

ジェネレータは、形式仕様中の明示ディレクティブを解釈します。

- `@input <type>` / `@output <type>` (`object|array|string|number|boolean|unknown`)
- `@pre <expr>` / `@post <expr>`
- `@state <A|B|C>` / `@transition <A -> B if condition>`

例:

```text
@input object
@output number
@pre input != null
@post output != null
@state Init|Validated|Done
@transition Init -> Validated if input != null
@transition Validated -> Done if output != null
```

> これは初期スケルトンです。将来版では、より具体的なフィールド単位の抽出が入る可能性があります。

### CI での任意 enforcement

環境変数 `CONTRACTS_ENFORCE=1` を設定すると、`contracts-exec` step は minimal な input/output parse と pre/post check が失敗した場合に PR を fail させます。既定は report-only です。

代替として、PR ラベル `enforce-contracts` を付与できます。verify workflow はそのラベルを検出し、その PR に対して `CONTRACTS_ENFORCE=1` を自動設定します。

### サンプル入力の与え方

`CONTRACTS_SAMPLE_INPUT=/path/to/input.json` を設定すると、JSON object を runtime contracts execution の入力として渡せます。schema や pre/post condition を現実的な shape で検証したい場合に有効です。未指定時は `{}` を使います。

代わりに `CONTRACTS_OPENAPI_PATH` を使うこともできます。既定値は `artifacts/codex/openapi.yaml` または `openapi.json` です。runner は OpenAPI document（JSON / YAML）から次の順序で best-effort にサンプルを導出します。

- まず最初の operation にある `requestBody.content['application/json'].schema` から入力を合成します。
- それが取れない場合は `components.schemas` の先頭 entry にフォールバックします。
- どちらも使えない場合は、最後に最初の path key を placeholder input shape として使います。

### 運用メモ

- unsupported directive や構造不足は `generationWarnings` で可視化されます。
- `enforce-contracts` が効くのは runtime-contracts lane だけで、無関係な formal checks は有効化しません。
- merge blocking が必要な PR にだけ opt-in enforcement を使ってください。
