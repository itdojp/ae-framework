#!/usr/bin/env node
// Non-blocking validator for apalache-summary.json shape.
import fs from 'node:fs';
import path from 'node:path';

const file = process.argv[2] || path.join('hermetic-reports','formal','apalache-summary.json');
if (!fs.existsSync(file)) {
  console.log(`No summary found: ${file}`);
  process.exit(0);
}
try {
  const j = JSON.parse(fs.readFileSync(file,'utf-8'));
  const req = ['tool','ran','status'];
  const missing = req.filter(k => !(k in j));
  if (missing.length) {
    console.warn(`Missing keys: ${missing.join(', ')}`);
  }
  // Soft checks
  if (j.ran === true) {
    if (!('ok' in j)) console.warn('Key ok is missing for ran=true');
    if (!('outputFile' in j)) console.warn('Key outputFile is missing for ran=true');
  }
  console.log('apalache-summary.json: validation complete (non-blocking)');
  process.exit(0);
} catch (e) {
  console.warn('Failed to parse apalache-summary.json (non-blocking):', e.message);
  process.exit(0);
}

