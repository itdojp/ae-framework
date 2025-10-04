#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';

function parseArgs() {
  const args = process.argv.slice(2);
  const result = { input: null, output: null };
  for (let i = 0; i < args.length; i++) {
    const arg = args[i];
    if ((arg === '--input' || arg === '-i') && args[i + 1]) {
      result.input = args[++i];
    } else if ((arg === '--output' || arg === '-o') && args[i + 1]) {
      result.output = args[++i];
    }
  }
  if (!result.input) {
    console.error('Usage: validate-kvonce --input <projection.json> [--output <json>]');
    process.exit(1);
  }
  return result;
}

function validate(projection) {
  const issues = [];

  for (const [key, entry] of Object.entries(projection.perKey ?? {})) {
    const successCount = entry.successCount ?? 0;
    if (successCount > 1) {
      issues.push({ key, type: 'multiple-success', message: `success appeared ${successCount} times` });
    }
    const duplicateFailures = (entry.failureReasons ?? []).filter((r) => r === 'duplicate');
    if (duplicateFailures.length > 0 && successCount === 0) {
      issues.push({ key, type: 'duplicate-without-success', message: 'duplicate failure emitted before any success' });
    }
    if ((entry.retries ?? 0) > 3) {
      issues.push({ key, type: 'retry-bound-exceeded', message: `retry count ${entry.retries} exceeded MAX_RETRIES 3` });
    }
  }

  return {
    generatedAt: new Date().toISOString(),
    valid: issues.length === 0,
    issues,
  };
}

const { input, output } = parseArgs();
const projection = JSON.parse(fs.readFileSync(input, 'utf8'));
const report = validate(projection);
const json = JSON.stringify(report, null, 2);

if (output) {
  fs.mkdirSync(path.dirname(output), { recursive: true });
  fs.writeFileSync(output, json);
} else {
  process.stdout.write(json);
}
