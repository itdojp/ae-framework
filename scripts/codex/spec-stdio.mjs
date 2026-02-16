#!/usr/bin/env node
// CodeX stdio bridge (no MCP): AE-Spec compile/validate/codegen tools
// Input: single-line JSON { action: 'compile|validate|codegen', args: {...} }
// Output: single-line JSON result { ok: boolean, data?: any, error?: string }

import fs from 'fs';
import path from 'path';
import { pathToFileURL } from 'url';

function respond(obj) {
  process.stdout.write(JSON.stringify(obj) + '\n');
}

function respondError(error, exitCode = 1) {
  process.exitCode = exitCode;
  respond({ ok: false, error });
}

async function loadSpecCompiler() {
  const importErrors = [];
  try {
    return await import('@ae-framework/spec-compiler');
  } catch (error) {
    importErrors.push(error instanceof Error ? error.message : String(error));
  }

  const localDist = path.resolve(process.cwd(), 'packages/spec-compiler/dist/index.js');
  if (!fs.existsSync(localDist)) {
    try {
      const { spawnSync } = await import('child_process');
      const build = spawnSync('pnpm', ['-s', '--filter', '@ae-framework/spec-compiler', 'build'], {
        cwd: process.cwd(),
        encoding: 'utf8',
      });
      if (build.status !== 0) {
        importErrors.push(`pnpm build failed: ${(build.stderr || build.stdout || '').trim()}`);
      }
    } catch (error) {
      importErrors.push(`failed to run pnpm build: ${error instanceof Error ? error.message : String(error)}`);
    }
  }

  if (fs.existsSync(localDist)) {
    try {
      return await import(pathToFileURL(localDist).href);
    } catch (error) {
      importErrors.push(error instanceof Error ? error.message : String(error));
    }
  }

  throw new Error(`Unable to load @ae-framework/spec-compiler (${importErrors.join(' | ')})`);
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
    let req;
    try {
      req = JSON.parse(line);
    } catch (error) {
      const message = error instanceof Error ? error.message : String(error);
      return respondError(`Invalid JSON input: ${message}`, 2);
    }
    const action = req.action;
    const args = req.args || {};

    if (!action) return respondError('Missing action', 2);

    switch (action) {
      case 'compile': {
        const { AESpecCompiler } = await loadSpecCompiler();
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
        const { AESpecCompiler } = await loadSpecCompiler();
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
        const failedTargets = [];
        for (const t of targets) {
          const dir = `${outBase}/${t}`;
          const runResult = run(t, dir);
          if (runResult.status !== 0) {
            failedTargets.push(t);
          }
          results[t] = dir;
        }
        if (failedTargets.length > 0) {
          return respondError(`Codegen failed for targets: ${failedTargets.join(', ')}`);
        }
        return respond({ ok: true, data: { outBase, results } });
      }
      default:
        return respondError(`Unknown action: ${action}`, 2);
    }
  } catch (err) {
    respondError(err instanceof Error ? err.message : String(err));
  }
}

main();
