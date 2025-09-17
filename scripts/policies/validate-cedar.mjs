#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';

function safeJson(p){
  try { return { ok: true, data: JSON.parse(fs.readFileSync(p, 'utf-8')) }; }
  catch (e) { return { ok: false, error: String(e && e.message || e) }; }
}

function list(dir){
  try { return fs.readdirSync(dir).map(f => path.join(dir, f)); } catch { return []; }
}

const baseDir = process.env.CEDAR_POLICIES_DIR || path.join('policies', 'cedar');
const outFile = process.env.CEDAR_SUMMARY || path.join('artifacts', 'policies', 'cedar-summary.json');
const repoRoot = process.cwd();
const files = list(baseDir).filter(p => fs.statSync(p).isFile());

const jsonFiles = files.filter(f => /\.json$/i.test(f));
const cedarFiles = files.filter(f => /\.(cedar|ced)$/i.test(f));

const results = [];
const errors = [];

for (const jf of jsonFiles){
  const r = safeJson(jf);
  if (!r.ok){
    errors.push({ file: jf, kind: 'json-parse', message: r.error });
    results.push({ file: jf, type: 'json', valid: false });
    continue;
  }
  // Minimal shape check: expect either a policySet array or policies list-like structure
  const j = r.data;
  const hasPolicySet = Array.isArray(j?.policySet);
  const hasPolicies = Array.isArray(j?.policies) || Array.isArray(j?.PolicySet) || Array.isArray(j?.Policy);
  const valid = hasPolicySet || hasPolicies;
  if (!valid) {
    errors.push({ file: jf, kind: 'schema-min', message: 'no policySet/policies array found' });
  }
  results.push({ file: jf, type: 'json', valid });
}

for (const cf of cedarFiles){
  // Treat as plain text; optionally ensure non-empty
  const txt = fs.readFileSync(cf, 'utf-8');
  const nonEmpty = txt.trim().length > 0;
  if (!nonEmpty) errors.push({ file: cf, kind: 'empty', message: 'cedar policy is empty' });
  results.push({ file: cf, type: 'cedar', valid: nonEmpty });
}

const summary = {
  tool: 'cedar-validator',
  dir: path.relative(repoRoot, baseDir),
  filesScanned: files.length,
  jsonFiles: jsonFiles.length,
  cedarFiles: cedarFiles.length,
  okCount: results.filter(r => r.valid).length,
  ngCount: results.filter(r => !r.valid).length,
  errors,
  results,
  timestamp: new Date().toISOString()
};

fs.mkdirSync(path.dirname(outFile), { recursive: true });
fs.writeFileSync(outFile, JSON.stringify(summary, null, 2));
console.log(`✓ cedar summary written: ${outFile}`);
console.log(`- files=${summary.filesScanned} ok=${summary.okCount} ng=${summary.ngCount}`);

// Non-blocking script
process.exit(0);

