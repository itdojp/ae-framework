#!/usr/bin/env node
// CodeX stdio bridge (no MCP): AE-Spec compile/validate/codegen tools
// Input: single-line JSON { action: 'compile|validate|codegen', args: {...} }
// Output: single-line JSON result { ok: boolean, data?: any, error?: string }

import fs from 'fs';
import path from 'path';

function respond(obj) {
  process.stdout.write(JSON.stringify(obj) + '\n');
}

async function main() {
  try {
    const input = await new Promise((resolve, reject) => {
      let buf = '';
      process.stdin.setEncoding('utf8');
      process.stdin.on('data', (d) => (buf += d));
      process.stdin.on('end', () => resolve(buf));
      process.stdin.on('error', reject);
    });
    const line = input.trim().split('\n').filter(Boolean).pop() || '{}';
    const req = JSON.parse(line);
    const action = req.action;
    const args = req.args || {};

    if (!action) return respond({ ok: false, error: 'Missing action' });

    switch (action) {
      case 'compile': {
        const { AESpecCompiler } = await import('../../packages/spec-compiler/src/index.js');
        const compiler = new AESpecCompiler();
        const prev = process.env.AE_SPEC_RELAXED;
        if (args.relaxed) process.env.AE_SPEC_RELAXED = '1';
        try {
          const ir = await compiler.compile({
            inputPath: path.resolve(args.inputPath),
            outputPath: args.outputPath ? path.resolve(args.outputPath) : undefined,
            validate: args.validate !== false,
          });
          const lint = await compiler.lint(ir);
          return respond({ ok: true, data: {
            outputPath: args.outputPath || null,
            summary: lint.summary,
            counts: { entities: ir.domain.length, apis: ir.api.length, usecases: ir.usecases.length },
          }});
        } finally {
          process.env.AE_SPEC_RELAXED = prev;
        }
      }
      case 'validate': {
        const { AESpecCompiler } = await import('../../packages/spec-compiler/src/index.js');
        const compiler = new AESpecCompiler();
        const prev = process.env.AE_SPEC_RELAXED;
        if (args.relaxed) process.env.AE_SPEC_RELAXED = '1';
        try {
          const ir = await compiler.compile({ inputPath: path.resolve(args.inputPath), validate: false });
          const lint = await compiler.lint(ir);
          const issues = lint.issues.slice(0, 100).map(i => ({ severity: i.severity, id: i.id, message: i.message, section: i.location?.section || 'root' }));
          const passed = lint.summary.errors === 0 && (args.maxWarnings == null || lint.summary.warnings <= args.maxWarnings);
          return respond({ ok: true, data: { passed, summary: lint.summary, issues } });
        } finally {
          process.env.AE_SPEC_RELAXED = prev;
        }
      }
      case 'codegen': {
        const { spawnSync } = await import('child_process');
        const irPath = path.resolve(args.irPath || '.ae/ae-ir.json');
        const outBase = args.outDir || 'generated';
        const targets = Array.isArray(args.targets) && args.targets.length ? args.targets : ['typescript','api','database'];
        const run = (t, dir) => spawnSync(process.execPath, ['dist/src/cli/index.js','codegen','generate','-i', irPath, '-o', path.resolve(dir), '-t', t], { stdio: 'inherit' });
        const results = {};
        for (const t of targets) {
          const dir = `${outBase}/${t}`;
          run(t, dir);
          results[t] = dir;
        }
        return respond({ ok: true, data: { outBase, results } });
      }
      default:
        return respond({ ok: false, error: `Unknown action: ${action}` });
    }
  } catch (err) {
    respond({ ok: false, error: err instanceof Error ? err.message : String(err) });
  }
}

main();

