#!/usr/bin/env node

import { spawnSync } from 'node:child_process';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

const DOC_CONSISTENCY_SCRIPT = path.resolve(__dirname, 'check-doc-consistency.mjs');
const CI_INDEX_SCRIPT = path.resolve(__dirname, 'check-ci-doc-index-consistency.mjs');
const RUNBOOK_COMMAND_SCRIPT = path.resolve(__dirname, 'check-runbook-command-blocks.mjs');
const DOC_TODO_MARKER_SCRIPT = path.resolve(__dirname, 'check-doc-todo-markers.mjs');

function hasOption(args, longName, shortName) {
  return args.some((arg) => arg === longName || (shortName && arg === shortName) || arg.startsWith(`${longName}=`));
}

export function filterArgsForCiIndex(args) {
  const filtered = [];
  for (let index = 0; index < args.length; index += 1) {
    const arg = args[index];
    if (arg === '--docs') {
      const next = args[index + 1];
      if (next && !next.startsWith('-')) {
        index += 1;
      }
      continue;
    }
    if (arg.startsWith('--docs=')) {
      continue;
    }
    filtered.push(arg);
  }
  return filtered;
}

function runNodeScript(scriptPath, args) {
  const result = spawnSync(process.execPath, [scriptPath, ...args], {
    stdio: 'inherit',
    env: process.env,
  });
  if (typeof result.status === 'number') {
    return result.status;
  }
  return 1;
}

export function main(argv = process.argv) {
  const args = argv.slice(2);
  const docsStatus = runNodeScript(DOC_CONSISTENCY_SCRIPT, args);
  if (docsStatus !== 0) {
    return docsStatus;
  }
  const hasDocsFilter = hasOption(args, '--docs');
  const wantsJson = hasOption(args, '--format') && args.some((arg, index) => {
    if (arg === '--format') {
      return args[index + 1] === 'json';
    }
    return arg === '--format=json';
  });
  const wantsHelp = hasOption(args, '--help', '-h');
  if (hasDocsFilter || wantsJson || wantsHelp) {
    return 0;
  }
  const ciIndexStatus = runNodeScript(CI_INDEX_SCRIPT, filterArgsForCiIndex(args));
  if (ciIndexStatus !== 0) {
    return ciIndexStatus;
  }
  const runbookStatus = runNodeScript(RUNBOOK_COMMAND_SCRIPT, filterArgsForCiIndex(args));
  if (runbookStatus !== 0) {
    return runbookStatus;
  }
  const todoMarkerStatus = runNodeScript(DOC_TODO_MARKER_SCRIPT, filterArgsForCiIndex(args));
  return todoMarkerStatus;
}

if (process.argv[1] && path.resolve(process.argv[1]) === __filename) {
  process.exit(main(process.argv));
}
