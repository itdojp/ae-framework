#!/usr/bin/env node
// CodeX Quickstart PoC
// - Runs ae-framework verify (quality gates)
// - Optionally runs UI scaffold (Phase 6)
// - Writes a short Markdown summary to artifacts/

import { spawnSync } from 'child_process';
import fs from 'fs';
import path from 'path';

const root = process.cwd();
const cliCandidates = [
  'dist/src/cli/index.js',
  'dist/cli.js',
];

function findCLI() {
  for (const p of cliCandidates) {
    const abs = path.join(root, p);
    if (fs.existsSync(abs)) return abs;
  }
  throw new Error(`ae CLI not found. Tried: ${cliCandidates.join(', ')}`);
}

function runNode(args, opts = {}) {
  const res = spawnSync(process.execPath, args, {
    stdio: 'inherit',
    env: { ...process.env, ...(opts.env || {}) },
  });
  return res.status ?? 1;
}

function ensureDir(p) {
  fs.mkdirSync(p, { recursive: true });
}

async function main() {
  const cli = findCLI();
  const artifactsDir = path.join(root, 'artifacts');
  ensureDir(artifactsDir);
  const summaryPath = path.join(artifactsDir, `codex-quickstart-summary.md`);

  // 1) Verify gates
  console.log('[codex] Running ae verify ...');
  const verifyCode = runNode([cli, 'verify'], { env: { AE_TYPES_STRICT: '1' } });

  // 2) Optional UI scaffold
  let uiCode = 0;
  if (process.env.CODEX_RUN_UI === '1') {
    console.log('[codex] Running ae ui-scaffold --components ...');
    uiCode = runNode([cli, 'ui-scaffold', '--components']);
  }

  // 3) Optional formal generation + OpenAPI
  let formalCode = 0;
  let formalOut = '';
  if (process.env.CODEX_RUN_FORMAL === '1') {
    try {
      console.log('[codex] Generating formal spec + OpenAPI ...');
      const { FormalAgent } = await import(path.resolve('dist/src/agents/formal-agent.js'));
      const agent = new FormalAgent({ outputFormat: 'tla+', validationLevel: 'comprehensive', generateDiagrams: false, enableModelChecking: true });
      const reqText = process.env.CODEX_FORMAL_REQ || 'Users can register, login, and view their dashboard.';
      const spec = await agent.generateFormalSpecification(reqText, 'tla+');
      const codexDir = path.join(artifactsDir, 'codex');
      ensureDir(codexDir);
      const tlaPath = path.join(codexDir, 'quickstart-formal.tla');
      fs.writeFileSync(tlaPath, spec.content, 'utf8');
      try {
        const openapi = await agent.createAPISpecification(reqText, 'openapi', { includeExamples: true, generateContracts: true });
        fs.writeFileSync(path.join(codexDir, 'quickstart-openapi.yaml'), openapi.content, 'utf8');
      } catch {}
      formalOut = tlaPath;
      formalCode = 0;
    } catch (e) {
      console.error('[codex] Formal generation failed:', e);
      formalCode = 1;
    }
  }

  const summary = [
    '# CodeX Quickstart Summary',
    '',
    `- Verify exit code: ${verifyCode}`,
    process.env.CODEX_RUN_UI === '1' ? `- UI scaffold exit code: ${uiCode}` : '- UI scaffold: skipped',
    process.env.CODEX_RUN_FORMAL === '1' ? `- Formal generation: ${formalCode === 0 ? 'ok' : 'failed'}${formalOut ? ` (${path.relative(root, formalOut)})` : ''}` : '- Formal generation: skipped',
    '',
    'Artifacts generated under artifacts/ as applicable.',
  ].join('\n');
  fs.writeFileSync(summaryPath, summary, 'utf8');
  console.log(`[codex] Wrote summary: ${summaryPath}`);

  if (verifyCode !== 0 || uiCode !== 0) {
    process.exit(1);
  }
}

main().catch(err => {
  console.error('[codex] Quickstart failed:', err);
  process.exit(1);
});
