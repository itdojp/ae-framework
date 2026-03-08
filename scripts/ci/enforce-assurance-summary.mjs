#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';

const summaryPath = process.argv[2] ?? 'artifacts/assurance/assurance-summary.json';
const resolvedSummary = path.resolve(summaryPath);

if (!fs.existsSync(resolvedSummary)) {
  console.error(`[assurance-enforce] summary not found at ${resolvedSummary}`);
  process.exit(1);
}

let summary;
try {
  summary = JSON.parse(fs.readFileSync(resolvedSummary, 'utf8'));
} catch (error) {
  console.error(`[assurance-enforce] failed to parse ${resolvedSummary}:`, error);
  process.exit(1);
}

const top = summary?.summary ?? {};
const claims = Array.isArray(summary?.claims) ? summary.claims : [];
const violations = [];

if ((top.claimCount ?? 0) < 1) violations.push('claimCount must be greater than zero');
if ((top.warningClaims ?? 0) > 0) violations.push(`warningClaims=${top.warningClaims}`);
if ((top.claimsMissingRequiredLanes ?? 0) > 0) {
  violations.push(`claimsMissingRequiredLanes=${top.claimsMissingRequiredLanes}`);
}
if ((top.claimsMissingRequiredEvidenceKinds ?? 0) > 0) {
  violations.push(`claimsMissingRequiredEvidenceKinds=${top.claimsMissingRequiredEvidenceKinds}`);
}
if ((top.unlinkedCounterexamples ?? 0) > 0) {
  violations.push(`unlinkedCounterexamples=${top.unlinkedCounterexamples}`);
}
if ((top.warningCount ?? 0) > 0) violations.push(`warningCount=${top.warningCount}`);

for (const claim of claims) {
  const claimId = String(claim?.claimId ?? 'unknown').trim() || 'unknown';
  const status = String(claim?.status ?? '').trim();
  const missingLanes = Array.isArray(claim?.missingLanes) ? claim.missingLanes : [];
  const missingEvidenceKinds = Array.isArray(claim?.missingEvidenceKinds) ? claim.missingEvidenceKinds : [];
  const independenceWarnings = Array.isArray(claim?.independenceWarnings) ? claim.independenceWarnings : [];
  const openCounterexamples = Number(claim?.counterexamples?.open ?? 0);

  if (status !== 'satisfied') {
    violations.push(`claim ${claimId} status=${status || 'unknown'}`);
  }
  if (missingLanes.length > 0) {
    violations.push(`claim ${claimId} missingLanes=${missingLanes.join(',')}`);
  }
  if (missingEvidenceKinds.length > 0) {
    violations.push(`claim ${claimId} missingEvidenceKinds=${missingEvidenceKinds.join(',')}`);
  }
  if (independenceWarnings.length > 0) {
    violations.push(`claim ${claimId} independenceWarnings=${independenceWarnings.join(',')}`);
  }
  if (openCounterexamples > 0) {
    violations.push(`claim ${claimId} openCounterexamples=${openCounterexamples}`);
  }
}

const lines = [
  '### Assurance Enforcement',
  `- summary: ${resolvedSummary}`,
  `- claimCount: ${top.claimCount ?? 'n/a'}`,
  `- warningClaims: ${top.warningClaims ?? 'n/a'}`,
  `- warningCount: ${top.warningCount ?? 'n/a'}`,
  `- unlinkedCounterexamples: ${top.unlinkedCounterexamples ?? 'n/a'}`,
];

if (violations.length === 0) {
  lines.push('- result: pass');
  console.log(lines.join('\n'));
  process.exit(0);
}

lines.push('- result: fail', '- violations:');
for (const violation of violations) {
  lines.push(`  - ${violation}`);
}
console.error(lines.join('\n'));
process.exit(1);
