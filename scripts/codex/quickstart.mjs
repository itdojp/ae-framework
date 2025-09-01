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

  // 1) Quality gates (skippable)
  let verifyCode = 0;
  let verifyLabel = 'skipped';
  if (process.env.CODEX_SKIP_QUALITY === '1') {
    console.log('[codex] Skipping quality gates (CODEX_SKIP_QUALITY=1)');
  } else {
    console.log('[codex] Running ae quality run ...');
    verifyCode = runNode([cli, 'quality', 'run'], { env: { AE_TYPES_STRICT: '1' } });
    verifyLabel = String(verifyCode);
  }

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
  let openapiPath = '';
  let contractsSummaryPath = '';
  let contractsCount = 0;
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
        openapiPath = path.join(codexDir, 'quickstart-openapi.yaml');
        fs.writeFileSync(openapiPath, openapi.content, 'utf8');
        // Enrich with minimal endpoint if no paths are present
        try {
          const { default: yaml } = await import('yaml');
          const doc = yaml.parse(fs.readFileSync(openapiPath, 'utf8')) || {};
          const hasPaths = doc.paths && Object.keys(doc.paths).length > 0;
          if (!hasPaths) {
            doc.openapi = doc.openapi || '3.0.3';
            doc.info = doc.info || { title: 'Quickstart API', version: '1.0.0' };
            doc.paths = {
              '/health': {
                get: {
                  operationId: 'healthCheck',
                  summary: 'Health check endpoint',
                  responses: {
                    '200': {
                      description: 'OK',
                      content: {
                        'application/json': {
                          schema: {
                            type: 'object',
                            properties: { status: { type: 'string' } },
                            required: ['status']
                          }
                        }
                      }
                    }
                  }
                }
              }
            };
            fs.writeFileSync(openapiPath, yaml.stringify(doc), 'utf8');
            console.log('[codex] OpenAPI enriched with /health endpoint');
          }
        } catch (e) {
          console.warn('[codex] Failed to enrich OpenAPI:', e?.message || e);
        }
      } catch {}
      try {
        const mc = await agent.runModelChecking(spec, []);
        fs.writeFileSync(path.join(codexDir, 'quickstart-model-check.json'), JSON.stringify(mc, null, 2), 'utf8');
        formalMC = 'ok';
      } catch { formalMC = 'failed'; }
      formalOut = tlaPath;
      formalCode = 0;

      // If we have an OpenAPI spec, generate contract/E2E test templates
      if (openapiPath && fs.existsSync(openapiPath)) {
        console.log('[codex] Generating contract/E2E test templates from OpenAPI ...');
        const genArgs = [path.resolve('scripts/codex/generate-contract-tests.mjs'), '--openapi', openapiPath, '--outDir', 'tests/api/generated'];
        const rc = runNode(genArgs);
        // Read summary file if available
        try {
          const sPath = path.join(codexDir, 'openapi-contract-tests.json');
          if (fs.existsSync(sPath)) {
            const s = JSON.parse(fs.readFileSync(sPath, 'utf8'));
            contractsSummaryPath = sPath;
            contractsCount = s.files || 0;
          }
        } catch {}
        if (rc !== 0) {
          console.warn('[codex] Contract test generation exited with non-zero status');
        }
      }
    } catch (e) {
      console.error('[codex] Formal generation failed:', e);
      formalCode = 1;
    }
  }

  const summary = [
    '# CodeX Quickstart Summary',
    '',
    process.env.CODEX_SKIP_QUALITY === '1' ? '- Quality gates: skipped' : `- Quality gates exit code: ${verifyCode}`,
    process.env.CODEX_RUN_UI === '1' ? `- UI scaffold exit code: ${uiCode}${process.env.CODEX_PHASE_STATE_FILE ? ' (state file provided)' : ''}` : '- UI scaffold: skipped',
    process.env.CODEX_RUN_FORMAL === '1' ? `- Formal generation: ${formalCode === 0 ? 'ok' : 'failed'}${formalOut ? ` (${path.relative(root, formalOut)})` : ''}${formalMC ? `, model-check: ${formalMC}` : ''}` : '- Formal generation: skipped',
    process.env.CODEX_RUN_FORMAL === '1' && openapiPath ? `- OpenAPI: ${path.relative(root, openapiPath)}${contractsSummaryPath ? ` → Generated contract/E2E templates: ${contractsCount}` : ''}` : '',
    '',
    'Artifacts generated under artifacts/ as applicable.',
  ].join('\n');
  fs.writeFileSync(summaryPath, summary, 'utf8');
  console.log(`[codex] Wrote summary: ${summaryPath}`);

  if (process.env.CODEX_TOLERANT === '1') {
    // Tolerant mode: never fail quickstart
    process.exit(0);
  }
  if (verifyCode !== 0 || uiCode !== 0) {
    process.exit(1);
  }
}

main().catch(err => {
  console.error('[codex] Quickstart failed:', err);
  process.exit(1);
});
