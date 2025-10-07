// Execute runtime contracts (optional, report-only)
// Uses tsx to run TypeScript directly in CI.

import { promises as fs } from 'fs';
import path from 'path';

type UnknownRecord = Record<string, unknown>;

const warn = (context: string, error: unknown) => {
  const message = error instanceof Error ? error.message : String(error);
  console.warn(`[contracts-exec] ${context}: ${message}`);
};

async function exists(p: string): Promise<boolean> {
  try {
    await fs.stat(p);
    return true;
  } catch (error) {
    const err = error as NodeJS.ErrnoException;
    if (err?.code !== 'ENOENT') {
      warn(`stat failed for ${p}`, error);
    }
    return false;
  }
}

const createSynthesizer = (allSchemas: Record<string, any>) => {
  const seen = new Set<string>();
  const synth = (schema: any, depth = 0): any => {
    if (!schema || depth > 5) return {};

    if (schema.$ref && typeof schema.$ref === 'string') {
      const ref = schema.$ref.split('/').pop() as string | undefined;
      if (ref && allSchemas[ref] && !seen.has(ref)) {
        seen.add(ref);
        const result = synth(allSchemas[ref], depth + 1);
        seen.delete(ref);
        return result;
      }
    }

    if (schema.default !== undefined) {
      return schema.default;
    }
    if (Array.isArray(schema.enum) && schema.enum.length > 0) {
      return schema.enum[0];
    }

    const derivedType = schema.type
      || (schema.properties ? 'object' : schema.items ? 'array' : 'string');

    switch (derivedType) {
      case 'integer':
      case 'number':
        return 0;
      case 'boolean':
        return false;
      case 'array': {
        const item = schema.items ? synth(schema.items, depth + 1) : null;
        return item === null || item === undefined ? [] : [item];
      }
      case 'object': {
        const obj: UnknownRecord = {};
        const required: string[] = Array.isArray(schema.required) ? schema.required : [];
        for (const [key, value] of Object.entries<any>(schema.properties || {})) {
          const synthesized = synth(value, depth + 1);
          obj[key] = synthesized;
          if (
            required.includes(key)
            && (synthesized === '' || synthesized === null || synthesized === undefined)
          ) {
            obj[key] = synthesized === '' ? 'REQUIRED' : (synthesized ?? 'REQUIRED');
          }
        }
        return obj;
      }
      default:
        return '';
    }
  };

  return synth;
};

const deriveSampleFromOpenApi = (oas: any): unknown | null => {
  if (!oas || typeof oas !== 'object') return null;

  const schemas = oas.components?.schemas ?? {};
  const names = Object.keys(schemas);
  const synth = createSynthesizer(schemas);

  const pathKeys: string[] = oas.paths ? Object.keys(oas.paths) : [];
  for (const pk of pathKeys) {
    const ops = oas.paths[pk];
    if (!ops || typeof ops !== 'object') continue;
    for (const method of Object.keys(ops)) {
      const operation = (ops as any)[method];
      const schema = operation?.requestBody?.content?.['application/json']?.schema;
      if (schema) {
        return synth(schema);
      }
    }
  }

  if (names.length > 0) {
    return synth(schemas[names[0]]);
  }

  if (pathKeys.length > 0) {
    return { path: pathKeys[0] };
  }

  return null;
};

const deriveSampleFromYaml = (text: string): unknown | null => {
  const jsonMatch = text.match(/\{[\s\S]*?\}/);
  if (!jsonMatch) return null;
  try {
    return JSON.parse(jsonMatch[0]);
  } catch (error) {
    warn('failed to parse JSON fragment from OpenAPI YAML', error);
    return null;
  }
};

const loadInputFromOpenApi = async (openapiPath: string): Promise<unknown | null> => {
  try {
    const contents = await fs.readFile(openapiPath, 'utf8');
    if (openapiPath.endsWith('.json')) {
      try {
        const oas = JSON.parse(contents);
        return deriveSampleFromOpenApi(oas);
      } catch (error) {
        warn(`failed to parse OpenAPI JSON at ${openapiPath}`, error);
        return null;
      }
    }
    return deriveSampleFromYaml(contents);
  } catch (error) {
    warn(`failed to read OpenAPI file at ${openapiPath}`, error);
    return null;
  }
};

async function main() {
  const repoRoot = process.cwd();
  const contractsDir = path.join(repoRoot, 'src', 'contracts');
  const present = {
    schemas: await exists(path.join(contractsDir, 'schemas.ts')),
    conditions: await exists(path.join(contractsDir, 'conditions.ts')),
    machine: await exists(path.join(contractsDir, 'machine.ts')),
  };

  const summary: any = { present, results: {}, note: 'Report-only execution of contracts' };

  if (present.schemas && present.conditions) {
    try {
      // Dynamic imports using tsx runner context
      // eslint-disable-next-line @typescript-eslint/ban-ts-comment
      // @ts-ignore – tsx resolves the path at runtime
      const schemas = await import(path.join(repoRoot, 'src', 'contracts', 'schemas.ts'));
      // eslint-disable-next-line @typescript-eslint/ban-ts-comment
      // @ts-ignore
      const conds = await import(path.join(repoRoot, 'src', 'contracts', 'conditions.ts'));

      let input: unknown = {};
      const samplePath = process.env.CONTRACTS_SAMPLE_INPUT;
      if (samplePath) {
        try {
          const txt = await fs.readFile(samplePath, 'utf8');
          input = JSON.parse(txt);
        } catch (error) {
          warn(`failed to read CONTRACTS_SAMPLE_INPUT at ${samplePath}`, error);
        }
      } else {
        const defaultYaml = path.join(repoRoot, 'artifacts', 'codex', 'openapi.yaml');
        const defaultJson = path.join(repoRoot, 'artifacts', 'codex', 'openapi.json');
        const openapiPath = process.env.CONTRACTS_OPENAPI_PATH
          || (await exists(defaultJson) ? defaultJson : defaultYaml);
        const derivedInput = await loadInputFromOpenApi(openapiPath);
        if (derivedInput !== null) {
          input = derivedInput;
        }
      }

      let parseInOk = true;
      let preOk = true;
      let postOk = true;
      let parseOutOk = true;

      try { schemas.InputSchema?.parse?.(input); } catch (error) { parseInOk = false; warn('InputSchema.parse failed', error); }
      try { preOk = !!conds.pre?.(input); } catch (error) { preOk = false; warn('conditions.pre failed', error); }

      const output: unknown = {};
      try { postOk = !!conds.post?.(input, output); } catch (error) { postOk = false; warn('conditions.post failed', error); }
      try { schemas.OutputSchema?.parse?.(output); } catch (error) { parseOutOk = false; warn('OutputSchema.parse failed', error); }

      summary.results = { parseInOk, preOk, postOk, parseOutOk };
    } catch (error) {
      summary.results = { error: String(error) };
      warn('contracts execution failed', error);
    }
  }

  const outDir = path.join(repoRoot, 'artifacts', 'contracts');
  await fs.mkdir(outDir, { recursive: true });
  await fs.writeFile(path.join(outDir, 'contracts-exec.json'), JSON.stringify(summary, null, 2));

  if (process.env.CONTRACTS_ENFORCE === '1') {
    const results = summary.results as Record<string, unknown> | undefined;
    const hasError = typeof results?.error === 'string';
    const flagNames = ['parseInOk', 'preOk', 'postOk', 'parseOutOk'] as const;
    const booleanFailure = flagNames.some((flag) => results && flag in results && results[flag] === false);
    if (hasError || booleanFailure) {
      console.error('contracts-exec enforcement failed: contract validation reported errors.');
      process.exit(2);
    }
  }

  console.log('Contracts exec summary written to artifacts/contracts/contracts-exec.json');
}

main().catch((error) => {
  console.error('contracts-exec failed:', error);
  process.exit(1);
});
