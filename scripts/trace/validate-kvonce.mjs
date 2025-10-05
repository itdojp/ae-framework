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

  const getAttempt = (context) => {
    if (context == null) return null;
    if (typeof context === 'number') return context;
    if (typeof context === 'string') return null;
    if (typeof context === 'object') {
      if (typeof context.attempt === 'number') return context.attempt;
      if (typeof context.attempts === 'number') return context.attempts;
    }
    return null;
  };

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

    const retryContexts = Array.isArray(entry.retryContexts) ? entry.retryContexts : [];
    if (retryContexts.length > 0) {
      const attempts = retryContexts.map(getAttempt);
      if (attempts.some((value) => value == null)) {
        issues.push({ key, type: 'retry-context-missing', message: 'retry event missing attempt number in context' });
      } else {
        for (let i = 0; i < attempts.length; i += 1) {
          if (attempts[i] !== i + 1) {
            issues.push({ key, type: 'retry-attempt-out-of-sequence', message: `retry attempt ${attempts[i]} expected ${i + 1}` });
            break;
          }
        }
      }

      const successContexts = Array.isArray(entry.successContexts) ? entry.successContexts : [];
      const successAttempt = successContexts.map(getAttempt).find((value) => value != null);
      if (successAttempt != null && successAttempt !== retryContexts.length + 1) {
        issues.push({ key, type: 'success-attempt-mismatch', message: `success attempt ${successAttempt} inconsistent with ${retryContexts.length} retries` });
      }
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
