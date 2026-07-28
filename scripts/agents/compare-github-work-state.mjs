#!/usr/bin/env node

import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { fileURLToPath } from 'node:url';
import {
  compareGitHubWorkStateSnapshots,
  readAndValidateGitHubWorkStateSnapshot,
} from './github-work-state-lib.mjs';

function readRequiredValue(argv, index, option) {
  const value = argv[index + 1];
  if (!value || value.startsWith('--')) throw new Error(`missing value for ${option}`);
  return value;
}

export function parseArgs(argv = process.argv.slice(2)) {
  const options = {
    baselinePath: null,
    currentPath: null,
    expectedHead: null,
    outputPath: null,
    help: false,
  };
  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--') {
      continue;
    } else if (arg === '--baseline') {
      options.baselinePath = readRequiredValue(argv, index, arg);
      index += 1;
    } else if (arg === '--current') {
      options.currentPath = readRequiredValue(argv, index, arg);
      index += 1;
    } else if (arg === '--expected-head') {
      options.expectedHead = readRequiredValue(argv, index, arg);
      index += 1;
    } else if (arg === '--output') {
      options.outputPath = readRequiredValue(argv, index, arg);
      index += 1;
    } else if (arg === '--help' || arg === '-h') {
      options.help = true;
    } else {
      throw new Error(`unknown option: ${arg}`);
    }
  }
  if (!options.help) {
    for (const [key, flag] of [
      ['baselinePath', '--baseline'],
      ['currentPath', '--current'],
      ['expectedHead', '--expected-head'],
      ['outputPath', '--output'],
    ]) {
      if (!options[key]) throw new Error(`${flag} is required`);
    }
  }
  return options;
}

function printHelp() {
  process.stdout.write(
    'Compare two GitHub work-state snapshots without network access.\n\n'
      + 'Usage:\n'
      + '  node scripts/agents/compare-github-work-state.mjs \\\n'
      + '    --baseline OLD.json --current NEW.json --expected-head SHA --output REPORT.json\n\n'
      + 'Exit codes: 0=no-state-change, 2=stale-context, 1=contract-invalid/error\n',
  );
}

function writeReport(outputPath, report) {
  const resolved = path.resolve(outputPath);
  fs.mkdirSync(path.dirname(resolved), { recursive: true });
  fs.writeFileSync(resolved, `${JSON.stringify(report, null, 2)}\n`, { encoding: 'utf8', mode: 0o600 });
  return resolved;
}

export function run(argv = process.argv.slice(2)) {
  const options = parseArgs(argv);
  if (options.help) {
    printHelp();
    return { exitCode: 0 };
  }

  let report;
  try {
    const baseline = readAndValidateGitHubWorkStateSnapshot(path.resolve(options.baselinePath));
    const current = readAndValidateGitHubWorkStateSnapshot(path.resolve(options.currentPath));
    report = compareGitHubWorkStateSnapshots(baseline, current, { expectedHead: options.expectedHead });
  } catch (error) {
    report = {
      schemaVersion: 'github-work-state-comparison/v1',
      status: 'contract-invalid',
      baselineDigest: null,
      currentDigest: null,
      changes: [],
      errors: [error instanceof Error ? error.message : String(error)],
    };
  }

  const outputPath = writeReport(options.outputPath, report);
  process.stdout.write(
    `[github-work-state] comparison=${report.status} report=${outputPath}\n`
      + `[github-work-state] baseline=${report.baselineDigest ?? 'invalid'} current=${report.currentDigest ?? 'invalid'}\n`,
  );
  if (report.status === 'no-state-change') return { exitCode: 0, report, outputPath };
  if (report.status === 'stale-context') return { exitCode: 2, report, outputPath };
  return { exitCode: 1, report, outputPath };
}

export function isExecutedAsMain(importMetaUrl, argvPath = process.argv[1]) {
  return Boolean(argvPath) && fileURLToPath(importMetaUrl) === path.resolve(argvPath);
}

if (isExecutedAsMain(import.meta.url)) {
  try {
    const result = run();
    process.exitCode = result.exitCode;
  } catch (error) {
    process.stderr.write(`[github-work-state] ${error instanceof Error ? error.message : String(error)}\n`);
    process.exitCode = 1;
  }
}
