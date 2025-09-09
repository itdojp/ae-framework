#!/usr/bin/env node
import { promises as fs } from 'fs';
import path from 'path';

const repoRoot = process.cwd();

async function exists(p) { try { await fs.stat(p); return true; } catch { return false; } }

async function main() {
  const schemaPath = path.join(repoRoot, 'src', 'contracts', 'schemas.ts');
  const condPath = path.join(repoRoot, 'src', 'contracts', 'conditions.ts');
  const machinePath = path.join(repoRoot, 'src', 'contracts', 'machine.ts');
  const summary = {
    present: {
      schemas: await exists(schemaPath),
      conditions: await exists(condPath),
      machine: await exists(machinePath)
    },
    note: 'Report-only. Future: execute runtime checks in verify.'
  };
  const outDir = path.join(repoRoot, 'artifacts', 'contracts');
  await fs.mkdir(outDir, { recursive: true });
  await fs.writeFile(path.join(outDir, 'contracts-check.json'), JSON.stringify(summary, null, 2));
  console.log('Contracts check summary written to artifacts/contracts/contracts-check.json');
}

// Report-only for now, but reflect failures with a non-zero code to surface issues.
main().catch((e) => { console.error('contracts-check failed:', e); process.exit(1); });
