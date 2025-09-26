#!/usr/bin/env node
import fs from 'node:fs';
import { execSync } from 'node:child_process';

const lines = [];

const readJson = (path) => {
  try {
    return JSON.parse(fs.readFileSync(path, 'utf8'));
  } catch {
    return null;
  }
};

const push = (line) => {
  if (line) lines.push(line);
};

const modelCheck = readJson('artifacts/codex/model-check.json');
if (modelCheck) {
  const props = Array.isArray(modelCheck.properties) ? modelCheck.properties.length : 0;
  const unsat = Array.isArray(modelCheck.properties)
    ? modelCheck.properties.filter((p) => p && p.satisfied === false).length
    : 0;
  push(`• Model Checking: ${props} properties, Unsatisfied: ${unsat}`);
}

const uiSummary = readJson('artifacts/codex/ui-summary.json');
if (uiSummary) {
  const files = Array.isArray(uiSummary.files) ? uiSummary.files : [];
  push(`• UI Scaffold: ${uiSummary.okEntities ?? 'n/a'}/${uiSummary.totalEntities ?? 'n/a'} entities, Files: ${files.length}, Dry-run: ${!!uiSummary.dryRun}`);
  if (files.length) {
    const preview = files.slice(0, 5).map((f) => `    - ${f}`).join('\n');
    push('  Preview files (up to 5):\n' + preview);
  }
}

const stories = readJson('artifacts/codex/result-stories.json');
if (stories) {
  const summary = stories.response?.summary ?? '';
  const storiesMatch = summary.match(/(\d+)\s+stor/i);
  const epicsMatch = summary.match(/(\d+)\s+epic/i);
  const parts = [];
  parts.push(storiesMatch ? `${storiesMatch[1]} stories` : 'stories: n/a');
  if (epicsMatch) parts.push(`${epicsMatch[1]} epics`);
  push(`• Stories: ${parts.join(', ')}`);
}

const validation = readJson('artifacts/codex/result-validation.json');
if (validation) {
  const summary = validation.response?.summary ?? 'Validation';
  const analysis = validation.response?.analysis ?? '';
  const coverageMatch = analysis.match(/Coverage:\s*(\d+)%/i);
  const coverage = coverageMatch ? `, Coverage: ${coverageMatch[1]}%` : '';
  push(`• Validation: ${summary}${coverage}`);
}

const intent = readJson('artifacts/codex/result-intent.json');
if (intent) {
  const summary = intent.response?.summary ?? '';
  const reqMatch = summary.match(/(\d+)\s+requirement/i);
  const reqText = reqMatch ? `${reqMatch[1]} requirements` : 'requirements: n/a';
  push(`• Intent: ${reqText}`);
}

if (fs.existsSync('artifacts/codex/formal.tla')) {
  push('• Formal: TLA+ generated (artifacts/codex/formal.tla)');
}
if (fs.existsSync('artifacts/codex/openapi.yaml')) {
  push('• OpenAPI: artifacts/codex/openapi.yaml');
}

const contractTests = readJson('artifacts/codex/openapi-contract-tests.json');
if (contractTests) {
  push(`• Contract/E2E templates: ${contractTests.files ?? 'n/a'} files (dir: ${contractTests.outDir ?? 'n/a'})`);
}

try {
  const pbtCount = parseInt(execSync("bash -lc 'ls tests/property/*.test.ts 2>/dev/null | wc -l'", { stdio: ['ignore', 'pipe', 'ignore'] }).toString().trim(), 10) || 0;
  const bddCount = parseInt(execSync("bash -lc 'rg -n \"^Feature:\" tests 2>/dev/null | wc -l'", { stdio: ['ignore', 'pipe', 'ignore'] }).toString().trim(), 10) || 0;
  push(`• Tests: PBT files=${pbtCount}, BDD features=${bddCount}`);
} catch {}

const formalSummary = readJson('hermetic-reports/formal/summary.json');
if (formalSummary) {
  const tag = (ok) => ok ? '[OK]' : '[WARN]';
  const info = '[INFO]';
  const parts = [];
  const conf = formalSummary.conformance;
  if (conf) {
    const schemaErrors = conf.schemaErrors ?? 'n/a';
    const invariantViolations = conf.invariantViolations ?? 'n/a';
    const violationRate = conf.violationRate ?? 'n/a';
    let firstInvariant = '';
    if (conf.firstInvariantViolation && conf.firstInvariantViolation.type !== undefined && conf.firstInvariantViolation.index !== undefined) {
      firstInvariant = `, first=${conf.firstInvariantViolation.type}@${conf.firstInvariantViolation.index}`;
    }
    let firstSchema = '';
    if (conf.firstSchemaError?.path) {
      firstSchema = `, firstSchemaPath=${conf.firstSchemaError.path}`;
    }
    let byType = '';
    if (conf.byType && typeof conf.byType === 'object') {
      const entries = Object.entries(conf.byType).filter(([, value]) => typeof value === 'number' && value > 0);
      if (entries.length) {
        byType = `, byType(${entries.map(([key, value]) => `${key}=${value}`).join(', ')})`;
      }
    }
    const ok = schemaErrors === 0 && invariantViolations === 0;
    parts.push(`${ok ? tag(true) : tag(false)} Conformance: schemaErrors=${schemaErrors}, invariantViolations=${invariantViolations}, rate=${violationRate}${firstInvariant}${firstSchema}${byType}`);
  }
  if (formalSummary.smt) {
    const st = formalSummary.smt.status;
    const t = st === 'ran' ? tag(true) : (st === 'solver_not_available' ? info : tag(false));
    const file = formalSummary.smt.file ? ` (${formalSummary.smt.file})` : '';
    parts.push(`${t} SMT: ${st}${file}`);
  }
  if (formalSummary.alloy) {
    const st = formalSummary.alloy.status;
    const t = st === 'ran' ? tag(true) : (st === 'tool_not_available' ? info : tag(false));
    const file = formalSummary.alloy.file ? ` (${formalSummary.alloy.file})` : '';
    parts.push(`${t} Alloy: ${st}${file}`);
  }
  if (formalSummary.tla) {
    const st = formalSummary.tla.status;
    const t = st === 'ran' ? tag(true) : (st === 'tool_not_available' ? info : tag(false));
    const file = formalSummary.tla.file ? ` ${formalSummary.tla.file}` : '';
    parts.push(`${t} TLA: ${st} (${formalSummary.tla.engine})${file}`);
  }
  if (parts.length) {
    push('• Formal summary: ' + parts.join('; '));
  }
}

try {
  const tlaCount = parseInt(execSync("bash -lc 'ls spec/tla/*.tla 2>/dev/null | wc -l'", { stdio: ['ignore', 'pipe', 'ignore'] }).toString().trim(), 10) || 0;
  const alloyCount = parseInt(execSync("bash -lc 'ls spec/alloy/*.als 2>/dev/null | wc -l'", { stdio: ['ignore', 'pipe', 'ignore'] }).toString().trim(), 10) || 0;
  push(`• Formal specs: TLA=${tlaCount}, Alloy=${alloyCount}`);
} catch {}

if (!lines.length) {
  lines.push('No CodeX artifacts found to summarize.');
}

const body = '### CodeX Artifacts Summary\n\n' + lines.map((line) => '- ' + line).join('\n') + '\n';
fs.writeFileSync('codex-summary.md', body);
console.log(body);
