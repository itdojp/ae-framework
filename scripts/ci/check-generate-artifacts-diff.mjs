#!/usr/bin/env node
import fs from 'node:fs';
import { appendSection } from './step-summary.mjs';

const [, , summaryFileArg] = process.argv;
const summaryFile = summaryFileArg ?? 'hermetic-reports/spec/generate-artifacts-diff.json';
if (!fs.existsSync(summaryFile)) {
  console.log('No summary generated.');
  appendSection('Generate Artifacts Drift', ['- summary file missing']);
  throw new Error('generate-artifacts diff summary missing');
}

const summary = JSON.parse(fs.readFileSync(summaryFile, 'utf8'));
const changedTargets = (summary.targets || []).filter((target) => target.hasChanges);

if (changedTargets.length === 0) {
  appendSection('Generate Artifacts Drift', ['- clean']);
  console.log('No generate-artifacts drift detected.');
  process.exit(0);
}

const lines = [`- generated at: ${summary.generatedAt || 'unknown'}`];
console.log('Detected drift in generated artifacts:');
for (const target of changedTargets) {
  lines.push(`- ${target.path}: CHANGED`);
  console.log(`- ${target.path}`);
  if (Array.isArray(target.files)) {
    for (const file of target.files.slice(0, 10)) {
      lines.push(`  - ${file.status} ${file.file}`);
      console.log(`  ${file.status} ${file.file}`);
    }
    if (target.files.length > 10) {
      const remaining = target.files.length - 10;
      const message = `  - … (${remaining} more)`;
      lines.push(message);
      console.log(message.trim());
    }
  }
}

appendSection('Generate Artifacts Drift', lines);
throw new Error('generate-artifacts drift detected');
