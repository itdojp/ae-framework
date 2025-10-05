#!/usr/bin/env node
import fs from 'node:fs';

const [, , summaryFileArg] = process.argv;
const summaryFile = summaryFileArg ?? 'hermetic-reports/spec/generate-artifacts-diff.json';
const stepSummary = process.env.GITHUB_STEP_SUMMARY;

const appendSummary = (lines) => {
  if (!stepSummary) return;
  fs.appendFileSync(stepSummary, `${lines.join('\n')}\n`);
};

if (!fs.existsSync(summaryFile)) {
  console.log('No summary generated.');
  appendSummary(['## Generate Artifacts Drift', '- summary file missing']);
  throw new Error('generate-artifacts diff summary missing');
}

const summary = JSON.parse(fs.readFileSync(summaryFile, 'utf8'));
const changedTargets = (summary.targets || []).filter((target) => target.hasChanges);

if (changedTargets.length === 0) {
  appendSummary(['## Generate Artifacts Drift', '- clean']);
  console.log('No generate-artifacts drift detected.');
  return;
}

const lines = ['## Generate Artifacts Drift', `Generated at: ${summary.generatedAt || 'unknown'}`];
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

appendSummary(lines);
throw new Error('generate-artifacts drift detected');
