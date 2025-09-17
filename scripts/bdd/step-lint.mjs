#!/usr/bin/env node
// BDD step lint (non-blocking):
// - Reads .ae/ae-ir.json and checks usecases[].steps[]
// - Ensures steps exist, descriptions are non-empty, and at least one validation step per usecase
// - Emits a markdown summary to stdout and writes JSON summary to artifacts
import fs from 'node:fs';
import path from 'node:path';

const irPath = process.env.AE_IR_PATH || '.ae/ae-ir.json';
const outJson = 'artifacts/spec/bdd-step-lint.json';
const outDir = path.dirname(outJson);
fs.mkdirSync(outDir, { recursive: true });

function readJson(p){ try { return JSON.parse(fs.readFileSync(p,'utf-8')); } catch { return null; } }

const ir = readJson(irPath);
if (!ir) {
  const result = { ok: false, reason: 'ae-ir-missing', issues: [] };
  fs.writeFileSync(outJson, JSON.stringify(result, null, 2));
  console.log('⚠️ BDD step lint: .ae/ae-ir.json not found (skipping)');
  process.exit(0);
}

const issues = [];
const report = [];
const usecases = Array.isArray(ir.usecases) ? ir.usecases : [];
for (const uc of usecases) {
  const name = uc?.name || '(unnamed usecase)';
  const steps = Array.isArray(uc?.steps) ? uc.steps : [];
  if (steps.length === 0) {
    issues.push({ usecase: name, kind: 'no-steps', message: 'Usecase has no steps' });
    continue;
  }
  let hasValidation = false;
  for (const s of steps) {
    const desc = (s?.description || '').trim();
    const type = s?.type || 'action';
    if (!desc) issues.push({ usecase: name, kind: 'empty-description', message: `Step #${s?.step ?? '?'} has empty description` });
    if (type === 'validation') hasValidation = true;
  }
  if (!hasValidation) issues.push({ usecase: name, kind: 'no-validation', message: 'Usecase has no validation step' });
}

const ok = issues.length === 0;
const summary = { ok, usecases: usecases.length, issuesCount: issues.length, issues };
fs.writeFileSync(outJson, JSON.stringify(summary, null, 2));

report.push('## BDD Step Lint');
report.push('');
report.push(`Usecases: ${usecases.length}`);
report.push(`Issues: ${issues.length}`);
if (issues.length) {
  const top = issues.slice(0, 10).map(i => `- ${i.usecase}: ${i.kind} — ${i.message}`);
  report.push('', ...top);
}
console.log(report.join('\n'));

// non-blocking
process.exit(0);

