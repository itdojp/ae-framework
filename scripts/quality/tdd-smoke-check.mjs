#!/usr/bin/env node
/**
 * Lightweight TDD quality gate.
 *
 * Runs a focused Vitest suite (tests/tdd-setup.test.ts) to ensure the base TDD
 * infrastructure stays healthy.  The command emits a short JSON summary that
 * the quality gate runner can consume when needed.
 */

import { spawnSync } from 'node:child_process';
import { stdout as processStdout } from 'node:process';

function runVitest() {
  const env = {
    ...process.env,
    NODE_ENV: process.env.NODE_ENV ?? 'test',
    VITEST_POOL_STRATEGY: process.env.VITEST_POOL_STRATEGY ?? 'forks',
  };

  const result = spawnSync(
    'pnpm',
    ['vitest', 'run', 'tests/tdd-setup.test.ts', '--run', '--reporter=json', '--passWithNoTests'],
    {
      encoding: 'utf8',
      env,
      maxBuffer: 1024 * 1024 * 20,
      stdio: ['ignore', 'pipe', 'pipe'],
    }
  );

  return result;
}

function parseVitestStats(output) {
  const trimmed = (output || '').trim();
  if (!trimmed) return null;

  try {
    // Vitest prints a single JSON object, so parsing the full output is safe.
    return JSON.parse(trimmed);
  } catch {
    return null;
  }
}

function main() {
  const result = runVitest();

  if (result.error) {
    console.error('❌ Failed to execute Vitest:', result.error.message);
    process.exit(1);
  }

  const stats = parseVitestStats(result.stdout) ?? {};
  const tests = stats.numTotalTests ?? 0;
  const failed = stats.numFailedTests ?? 0;
  const suites = stats.numTotalTestSuites ?? 0;

  if ((result.status ?? 1) !== 0 || failed > 0) {
    console.error('❌ TDD smoke check failed.');
    if (result.stderr) {
      console.error(result.stderr.trim());
    }
    process.exit(result.status ?? 1);
  }

  const summary = {
    suite: 'tdd-smoke',
    tests,
    failed,
    suites,
    timestamp: new Date().toISOString(),
  };

  processStdout.write(JSON.stringify(summary) + '\n');
  console.log('0 error tdd-smoke');
  console.log('0 warning tdd-smoke');
}

main();
