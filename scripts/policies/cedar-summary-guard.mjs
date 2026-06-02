#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import { pathToFileURL } from 'node:url';

const DEFAULT_SUMMARY = path.join('artifacts', 'policies', 'cedar-summary.json');

export function readCedarSummary(summaryPath = DEFAULT_SUMMARY) {
  const resolved = path.resolve(summaryPath);
  let parsed;
  try {
    parsed = JSON.parse(fs.readFileSync(resolved, 'utf8'));
  } catch (error) {
    throw new Error(`failed to read Cedar summary ${resolved}: ${error?.message ?? String(error)}`);
  }
  return parsed;
}

export function requireNonNegativeInteger(value, fieldName) {
  if (!Number.isSafeInteger(value) || value < 0) {
    throw new Error(`Cedar summary field ${fieldName} must be a non-negative safe integer`);
  }
  return value;
}

export function cedarSummaryCounts(summary) {
  return {
    files: requireNonNegativeInteger(summary?.filesScanned, 'filesScanned'),
    ok: requireNonNegativeInteger(summary?.okCount, 'okCount'),
    ng: requireNonNegativeInteger(summary?.ngCount, 'ngCount'),
  };
}

export function writeGithubOutput(counts, outputPath = process.env.GITHUB_OUTPUT) {
  if (!outputPath) {
    throw new Error('GITHUB_OUTPUT is required to write Cedar summary outputs');
  }
  const lines = [
    `files=${requireNonNegativeInteger(counts.files, 'files')}`,
    `ok=${requireNonNegativeInteger(counts.ok, 'ok')}`,
    `ng=${requireNonNegativeInteger(counts.ng, 'ng')}`,
  ];
  fs.appendFileSync(outputPath, `${lines.join('\n')}\n`, 'utf8');
}

export function enforceCedarSummary(summary) {
  const counts = cedarSummaryCounts(summary);
  if (counts.ng > 0) {
    throw new Error(`Cedar validation found NG=${counts.ng} (enforce-security)`);
  }
  return counts;
}

function parseArgs(argv = process.argv.slice(2)) {
  const args = {
    summary: DEFAULT_SUMMARY,
    writeOutput: false,
    enforce: false,
  };
  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--summary' && argv[index + 1]) {
      args.summary = argv[index + 1];
      index += 1;
    } else if (arg.startsWith('--summary=')) {
      args.summary = arg.slice('--summary='.length);
    } else if (arg === '--write-output') {
      args.writeOutput = true;
    } else if (arg === '--enforce') {
      args.enforce = true;
    } else if (arg === '--help' || arg === '-h') {
      args.help = true;
    } else {
      throw new Error(`unknown argument: ${arg}`);
    }
  }
  return args;
}

export function main(argv = process.argv.slice(2), env = process.env) {
  const args = parseArgs(argv);
  if (args.help) {
    console.log('Usage: node scripts/policies/cedar-summary-guard.mjs [--summary <path>] [--write-output] [--enforce]');
    return 0;
  }
  const summary = readCedarSummary(args.summary);
  const counts = args.enforce ? enforceCedarSummary(summary) : cedarSummaryCounts(summary);
  if (args.writeOutput) {
    writeGithubOutput(counts, env.GITHUB_OUTPUT);
  }
  console.log(`Cedar summary validated: files=${counts.files} ok=${counts.ok} ng=${counts.ng}`);
  return 0;
}

if (process.argv[1] && pathToFileURL(path.resolve(process.argv[1])).href === import.meta.url) {
  try {
    process.exit(main());
  } catch (error) {
    console.error(error?.message ?? String(error));
    process.exit(1);
  }
}
