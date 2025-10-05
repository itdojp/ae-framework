#!/usr/bin/env node
import fs from 'node:fs';

const [, , summaryPath] = process.argv;
if (!summaryPath) {
  console.error('[render-generate-artifacts-summary] usage: render-generate-artifacts-summary.mjs <summary.json>');
  process.exit(1);
}

try {
  const data = JSON.parse(fs.readFileSync(summaryPath, 'utf8'));
  if (data.generatedAt) {
    console.log(`Generated at: ${data.generatedAt}`);
  }
  for (const target of data.targets || []) {
    const status = target.hasChanges ? 'CHANGED' : 'clean';
    console.log(`- ${target.path}: ${status}`);
    if (target.hasChanges && Array.isArray(target.files)) {
      const sample = target.files.slice(0, 10);
      for (const file of sample) {
        console.log(`  • ${file.status} ${file.file}`);
      }
      if (target.files.length > sample.length) {
        console.log(`  • … (${target.files.length - sample.length} more)`);
      }
    }
  }
} catch (error) {
  console.log(`Failed to read diff summary: ${error.message}`);
  process.exitCode = 1;
}
