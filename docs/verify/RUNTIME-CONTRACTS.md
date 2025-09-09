## Runtime Contracts from Formal Specs (Week 3)

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

### Supplying sample input

Set `CONTRACTS_SAMPLE_INPUT=/path/to/input.json` to feed a JSON object as input to the runtime contracts execution. This helps validate schemas and pre/post on a realistic shape. When absent, `{}` is used.

Alternatively, set `CONTRACTS_OPENAPI_PATH` (defaults to `artifacts/codex/openapi.yaml`) and the runner will try to extract the first JSON block it finds in the OpenAPI file as a sample input (best‑effort, optional).
