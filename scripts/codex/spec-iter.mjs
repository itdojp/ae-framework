#!/usr/bin/env node
// Semi-automated iteration driver for CodeX workflows.
// Iterations:
//  1) validate (lenient) -> collect issues
//  2) emit an instruction prompt for LLM to revise the AE‑Spec
//  3) wait for user/LLM to update the file, then continue
// Stops when strict compile passes or max iterations reached.

import { spawnSync } from 'child_process';
import fs from 'fs';
import path from 'path';

function runStdio(action, args) {
  const req = JSON.stringify({ action, args });
  const res = spawnSync('pnpm', ['run', 'codex:spec:stdio'], {
    input: req + '\n',
    encoding: 'utf8',
  });
  if (res.error) throw res.error;
  const line = (res.stdout || '').trim().split('\n').filter(Boolean).pop() || '{}';
  try { return JSON.parse(line); } catch (e) { return { ok: false, error: 'invalid-json', raw: line }; }
}

function write(file, txt) {
  fs.mkdirSync(path.dirname(file), { recursive: true });
  fs.writeFileSync(file, txt, 'utf8');
}

function buildRevisionPrompt(issues) {
  const bullets = issues.map(i => `- [${i.severity}] ${i.message} (section: ${i.section})`).join('\n');
  return `Please revise the AE‑Spec to address the following validator findings. Preserve prior valid content.\n\nConstraints:\n- Use field types only from: string|number|boolean|date|uuid|email|url|json|array|object\n- If enum-like fields are used, map to a supported base type (e.g., string)\n- Ensure invariants reference existing entities\n- Ensure API paths start with '/' and format list items as '- METHOD /path - summary'\n\nFindings:\n${bullets}\n\nProduce updated AE‑Spec content in Markdown with sections: Glossary, Domain, Invariants, Use Cases, API, UI, NFR.`;
}

async function main() {
  const args = process.argv.slice(2);
  if (args.length === 0) {
    console.log('Usage: node scripts/codex/spec-iter.mjs <spec-path> [maxIter=5] [maxWarnings=10]');
    process.exit(0);
  }
  const spec = args[0];
  const maxIter = parseInt(args[1] || '5', 10);
  const maxWarnings = parseInt(args[2] || '10', 10);
  const artifactsDir = 'artifacts/spec-iterate';

  console.log(`[iter] Starting iteration for ${spec} (maxIter=${maxIter}, maxWarnings=${maxWarnings})`);

  for (let i = 1; i <= maxIter; i++) {
    console.log(`\n[iter] ${i}/${maxIter} validate (lenient)`);
    const v = runStdio('validate', { inputPath: spec, relaxed: true, maxWarnings });
    if (!v.ok) { console.error('[iter] validate failed:', v.error || v.raw); process.exit(1); }
    const { passed, summary, issues } = v.data;
    write(`${artifactsDir}/issues-${String(i).padStart(2,'0')}.json`, JSON.stringify(v.data, null, 2));
    console.log(`[iter] lenient summary: errors=${summary.errors}, warnings=${summary.warnings}`);

    if (summary.errors === 0 && summary.warnings <= maxWarnings) {
      console.log(`[iter] Attempt strict compile → .ae/ae-ir.json`);
      const c = runStdio('compile', { inputPath: spec, outputPath: '.ae/ae-ir.json', relaxed: false, validate: true });
      if (c.ok) {
        console.log('[iter] strict compile ok, run codegen (typescript, api, database)');
        const g = runStdio('codegen', { irPath: '.ae/ae-ir.json', targets: ['typescript','api','database'] });
        if (!g.ok) console.warn('[iter] codegen returned:', g.error || g.data);
        console.log('[iter] done');
        process.exit(0);
      } else {
        console.log('[iter] strict compile failed, continue iterations');
      }
    }

    const prompt = buildRevisionPrompt(issues || []);
    const promptPath = `${artifactsDir}/rev-prompt-${String(i).padStart(2,'0')}.md`;
    write(promptPath, prompt);
    console.log(`[iter] Wrote revision prompt → ${promptPath}`);
    console.log('[iter] Please revise the spec accordingly, then press Enter to continue...');
    await new Promise(res => process.stdin.once('data', () => res(null)));
  }

  console.log(`[iter] Reached max iterations (${maxIter}) without strict pass.`);
  process.exit(1);
}

main().catch(e => { console.error('[iter] fatal:', e?.message || String(e)); process.exit(1); });
