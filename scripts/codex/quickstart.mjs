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
    const stateFile = process.env.CODEX_PHASE_STATE_FILE;
    if (stateFile) {
      console.log(`[codex] Running ui-scaffold-cli generate --state=${stateFile} ...`);
      const uiCli = path.resolve('dist/src/cli/ui-scaffold-cli.js');
      const args = [uiCli, 'generate', '--state', stateFile, '--output', '.', process.env.CODEX_UI_DRY_RUN === '0' ? '' : '--dry-run'].filter(Boolean);
      uiCode = runNode(args);
    } else {
      console.log('[codex] Running ae ui-scaffold --components ...');
      uiCode = runNode([cli, 'ui-scaffold', '--components']);
    }
  }

  // 3) Optional formal generation + OpenAPI
  let formalCode = 0;
  let formalOut = '';
  let formalMC = '';
  let formalMC = '';
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
      try {
        const mc = await agent.runModelChecking(spec, []);
        fs.writeFileSync(path.join(codexDir, 'quickstart-model-check.json'), JSON.stringify(mc, null, 2), 'utf8');
        formalMC = 'ok';
      } catch { formalMC = 'failed'; }
      formalOut = tlaPath;
      formalCode = 0;
    } catch (e) {
      console.error('[codex] Formal generation failed:', e);
      formalCode = 1;
    }
  }

  // Enrich summary from artifacts
  const codexDir = path.join(artifactsDir, 'codex');
  function readJSON(p) { try { return JSON.parse(fs.readFileSync(p, 'utf8')); } catch { return null; } }
  const uiSummary = readJSON(path.join(codexDir, 'ui-summary.json'));
  const uiResult = readJSON(path.join(codexDir, 'result-ui.json'));
  const formalResult = readJSON(path.join(codexDir, 'result-formal.json'));

  const lines = [
    '# CodeX Quickstart Summary',
    '',
    `- Verify exit code: ${verifyCode}`,
    process.env.CODEX_RUN_UI === '1' ? `- UI scaffold exit code: ${uiCode}${process.env.CODEX_PHASE_STATE_FILE ? ' (state file provided)' : ''}` : '- UI scaffold: skipped',
    process.env.CODEX_RUN_FORMAL === '1' ? `- Formal generation: ${formalCode === 0 ? 'ok' : 'failed'}${formalOut ? ` (${path.relative(root, formalOut)})` : ''}${formalMC ? `, model-check: ${formalMC}` : ''}` : '- Formal generation: skipped',
    '',
  ];
  if (uiSummary) {
    const files = uiSummary.files || [];
    const preview = files.slice(0, 5).map(f => `  - ${f}`);
    const more = files.length > 5 ? ` (+${files.length - 5} more)` : '';
    lines.push(`UI: ${uiSummary.okEntities}/${uiSummary.totalEntities} entities, Files: ${files.length}${more}, Dry-run: ${!!uiSummary.dryRun}`);
    if (preview.length) {
      lines.push('Preview files (up to 5):', ...preview);
    }
  }
  if (uiResult?.response) {
    const r = uiResult.response;
    lines.push(`UI Warnings: ${r.warnings?.length || 0}${r.shouldBlockProgress ? ' (BLOCKED)' : ''}`);
  }
  if (formalResult?.response) {
    const r = formalResult.response;
    lines.push(`Formal Warnings: ${r.warnings?.length || 0}${r.shouldBlockProgress ? ' (BLOCKED)' : ''}`);
  }
  lines.push('Artifacts generated under artifacts/ as applicable.');
  fs.writeFileSync(summaryPath, lines.join('\n'), 'utf8');
  console.log(`[codex] Wrote summary: ${summaryPath}`);

  const blocked = (uiResult?.response?.shouldBlockProgress || false) || (formalResult?.response?.shouldBlockProgress || false);
  if (verifyCode !== 0 || uiCode !== 0 || blocked) {
    process.exit(1);
  }
}

main().catch(err => {
  console.error('[codex] Quickstart failed:', err);
  process.exit(1);
});
