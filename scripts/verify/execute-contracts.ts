// Execute runtime contracts (optional, report-only)
// Uses tsx to run TypeScript directly in CI.

import { promises as fs } from 'fs';
import path from 'path';

async function exists(p: string) {
  try { await fs.stat(p); return true; } catch { return false; }
}

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
      // @ts-ignore
      const schemas = await import(path.join(repoRoot, 'src', 'contracts', 'schemas.ts'));
      // eslint-disable-next-line @typescript-eslint/ban-ts-comment
      // @ts-ignore
      const conds = await import(path.join(repoRoot, 'src', 'contracts', 'conditions.ts'));
      // Prefer sample input via env if provided
      let input: unknown = {};
      const samplePath = process.env.CONTRACTS_SAMPLE_INPUT;
      if (samplePath) {
        try {
          const txt = await fs.readFile(samplePath, 'utf8');
          input = JSON.parse(txt);
        } catch (e) {
          console.warn(`[contracts-exec] Warning: failed to read CONTRACTS_SAMPLE_INPUT at ${samplePath}: ${e instanceof Error ? e.message : String(e)}`);
        }
      } else {
        // Try to derive from OpenAPI when sample not provided
        const defaultYaml = path.join(repoRoot, 'artifacts', 'codex', 'openapi.yaml');
        const defaultJson = path.join(repoRoot, 'artifacts', 'codex', 'openapi.json');
        const openapiPath = process.env.CONTRACTS_OPENAPI_PATH || (await exists(defaultJson) ? defaultJson : defaultYaml);
        try {
          const txt = await fs.readFile(openapiPath, 'utf8');
          if (openapiPath.endsWith('.json')) {
            try {
              const oas = JSON.parse(txt);
              const schemas = oas.components?.schemas ?? {};
              const schemaNames = Object.keys(schemas);
              const seen = new Set<string>();
              const synth = (schema: any, depth = 0): any => {
                if (!schema || depth > 5) return {};
                if (typeof schema.$ref === 'string') {
                  const ref = schema.$ref.split('/').pop() as string | undefined;
                  if (ref && schemas[ref] && !seen.has(ref)) {
                    seen.add(ref);
                    const resolved = synth(schemas[ref], depth + 1);
                    seen.delete(ref);
                    return resolved;
                  }
                }
                if (schema.default !== undefined) return schema.default;
                if (Array.isArray(schema.enum) && schema.enum.length > 0) return schema.enum[0];
                const inferredType = schema.type || (schema.properties ? 'object' : (schema.items ? 'array' : 'string'));
                switch (inferredType) {
                  case 'integer':
                  case 'number':
                    return 0;
                  case 'boolean':
                    return false;
                  case 'array': {
                    const item = schema.items ? synth(schema.items, depth + 1) : null;
                    return item === null ? [] : [item];
                  }
                  case 'object': {
                    const obj: Record<string, unknown> = {};
                    const requiredKeys: string[] = Array.isArray(schema.required) ? schema.required : [];
                    const properties = schema.properties ? Object.entries<any>(schema.properties) : [];
                    for (const [key, value] of properties) {
                      obj[key] = synth(value, depth + 1);
                      if (requiredKeys.includes(key) && (obj[key] === '' || obj[key] === null || obj[key] === undefined)) {
                        obj[key] = obj[key] === '' ? 'REQUIRED' : obj[key];
                      }
                    }
                    return obj;
                  }
                  default:
                    return '';
                }
              };
              const deriveFromRequestBodies = (): unknown => {
                const paths = oas.paths ? Object.keys(oas.paths) : [];
                for (const route of paths) {
                  const operations = oas.paths?.[route];
                  if (!operations) continue;
                  for (const method of Object.keys(operations)) {
                    const operation = (operations as Record<string, any>)[method];
                    const requestSchema = operation?.requestBody?.content?.['application/json']?.schema;
                    if (requestSchema) {
                      return synth(requestSchema);
                    }
                  }
                }
                return undefined;
              };
              const derivedFromRequests = deriveFromRequestBodies();
              if (derivedFromRequests !== undefined) {
                input = derivedFromRequests;
              } else if (schemaNames.length > 0) {
                input = synth(schemas[schemaNames[0]]);
              } else {
                const pathKeys: string[] = oas.paths ? Object.keys(oas.paths) : [];
                if (pathKeys.length > 0) {
                  input = { path: pathKeys[0] };
                }
              }
            } catch (inferenceError) {
              console.debug('[contracts-exec] Debug: failed to derive sample input from OpenAPI schema:', inferenceError);
              void inferenceError; // Best-effort inference; fall back to empty input when parsing fails
            }
          } else {
            // YAML: try to extract first JSON block as a best-effort
            const jsonMatch = txt.match(/\{[\s\S]*?\}/);
            if (jsonMatch) {
              try {
                input = JSON.parse(jsonMatch[0]);
              } catch (parseError) {
                console.debug('Ignored error parsing JSON block from YAML, falling back to defaults:', parseError);
                void parseError; // ignore, fallback to defaults below
              }
            }
          }
        } catch (loaderError) {
          console.debug(`[contracts-exec] Debug: failed to load OpenAPI sample input at ${openapiPath}:`, loaderError);
          void loaderError; // ignore loader failures and keep default input
        }
      }
      let parseInOk = true;
      let parseOutOk = true;
      let preOk: boolean;
      let postOk: boolean;
      try { schemas.InputSchema?.parse?.(input); } catch (e) { parseInOk = false; }
      try { preOk = !!conds.pre?.(input); } catch (e) { preOk = false; }
      const output: unknown = {};
      try { postOk = !!conds.post?.(input, output); } catch (e) { postOk = false; }
      try { schemas.OutputSchema?.parse?.(output); } catch (e) { parseOutOk = false; }
      summary.results = { parseInOk, preOk, postOk, parseOutOk };
    } catch (e) {
      summary.results = { error: String(e) };
    }
  }

  const outDir = path.join(repoRoot, 'artifacts', 'contracts');
  await fs.mkdir(outDir, { recursive: true });
  await fs.writeFile(path.join(outDir, 'contracts-exec.json'), JSON.stringify(summary, null, 2));
  console.log('Contracts exec summary written to artifacts/contracts/contracts-exec.json');
}

main().catch((e) => { console.error('contracts-exec failed:', e); process.exit(1); });
