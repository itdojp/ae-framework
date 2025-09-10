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
              // Prefer deriving from components.schemas
              const schemas = oas.components?.schemas || {};
              const names = Object.keys(schemas);
              const seen = new Set<string>();
              const synth = (schema: any, depth = 0): any => {
                if (!schema || depth > 5) return {};
                if (schema.$ref && typeof schema.$ref === 'string') {
                  const ref = schema.$ref.split('/').pop() as string;
                  if (ref && schemas[ref] && !seen.has(ref)) {
                    seen.add(ref);
                    const v = synth(schemas[ref], depth + 1);
                    seen.delete(ref);
                    return v;
                  }
                }
                if (schema.default !== undefined) return schema.default;
                if (Array.isArray(schema.enum) && schema.enum.length > 0) return schema.enum[0];
                const t = schema.type || (schema.properties ? 'object' : (schema.items ? 'array' : 'string'));
                switch (t) {
                  case 'integer':
                  case 'number': return 0;
                  case 'boolean': return false;
                  case 'array': {
                    const item = schema.items ? synth(schema.items, depth + 1) : null;
                    return item === null ? [] : [item];
                  }
                  case 'object': {
                    const obj: any = {};
                    const req: string[] = Array.isArray(schema.required) ? schema.required : [];
                    for (const [k, v] of Object.entries<any>(schema.properties || {})) {
                      obj[k] = synth(v, depth + 1);
                      if (req.includes(k) && (obj[k] === '' || obj[k] === null || obj[k] === undefined)) {
                        obj[k] = obj[k] === '' ? 'REQUIRED' : obj[k];
                      }
                    }
                    return obj;
                  }
                  default: return '';
                }
              };
              if (names.length > 0) {
                input = synth((schemas as any)[names[0]]);
              } else {
                // Fallback: pick first path+op and build an object with the path only
                const paths = oas.paths ? Object.keys(oas.paths) : [];
                if (paths.length > 0) input = { path: paths[0] };
              }
            } catch {}
          } else {
            // YAML: try to extract first JSON block as a best-effort
            const jsonMatch = txt.match(/\{[\s\S]*?\}/);
            if (jsonMatch) {
              try { input = JSON.parse(jsonMatch[0]); } catch {}
            }
          }
        } catch {}
      }
      let preOk = true; let postOk = true; let parseInOk = true; let parseOutOk = true;
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
