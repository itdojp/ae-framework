#!/usr/bin/env node
// Convenience tools for AE-Spec workflows (no LLM required here)
// Usage:
//  pnpm run spec:validate:relaxed -- spec/feature.ae-spec.md
//  pnpm run spec:validate:strict -- spec/feature.ae-spec.md
//  pnpm run spec:compile -- spec/feature.ae-spec.md .ae/ae-ir.json
//  pnpm run spec:codegen -- .ae/ae-ir.json typescript,api,database

import path from 'path';
import { fileURLToPath } from 'url';
import { spawnSync } from 'child_process';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

function die(msg) { console.error(msg); process.exit(1); }
function run(args, env={}) {
  const res = spawnSync(process.execPath, ['dist/src/cli/index.js', ...args], { stdio: 'inherit', env: { ...process.env, ...env } });
  if (res.error) die(res.error.message);
  return res.status ?? 0;
}

async function main() {
  const [,, cmd, ...rest] = process.argv;
  if (!cmd) {
    console.log('Commands: validate-relaxed <spec>, validate-strict <spec>, compile <spec> [out=.ae/ae-ir.json], codegen [ir=.ae/ae-ir.json] [targets=typescript,api,database]');
    process.exit(0);
  }
  switch (cmd) {
    case 'validate-relaxed': {
      const spec = rest[0];
      if (!spec) die('spec path required');
      process.exit(run(['spec','validate','--relaxed','-i', spec, '--max-warnings','999']));
    }
    case 'validate-strict': {
      const spec = rest[0];
      if (!spec) die('spec path required');
      process.exit(run(['spec','validate','-i', spec]));
    }
    case 'compile': {
      const spec = rest[0];
      const out = rest[1] || '.ae/ae-ir.json';
      if (!spec) die('spec path required');
      process.exit(run(['spec','compile','-i', spec, '-o', out]));
    }
    case 'codegen': {
      const ir = rest[0] || '.ae/ae-ir.json';
      const targets = (rest[1] || 'typescript,api,database').split(',').map(s => s.trim()).filter(Boolean);
      // Run each target
      for (const t of targets) {
        const outDir = `generated/${t}`;
        const status = run(['codegen','generate','-i', ir, '-o', outDir, '-t', t]);
        if (status !== 0) process.exit(status);
      }
      process.exit(0);
    }
    default:
      die(`unknown command: ${cmd}`);
  }
}

main();

