#!/usr/bin/env node
import fs from 'node:fs';
import { validateArtifactProvenance } from './lib/artifact-provenance.mjs';

const expectedFlagMap = new Map([
  ['--artifact-name', 'artifactName'],
  ['--repository', 'repository'],
  ['--workflow', 'workflow'],
  ['--workflow-ref', 'workflowRef'],
  ['--workflow-ref-prefix', 'workflowRefPrefix'],
  ['--run-id', 'runId'],
  ['--run-attempt', 'runAttempt'],
  ['--event-name', 'eventName'],
  ['--head-sha', 'headSha'],
  ['--base-sha', 'baseSha'],
  ['--head-repository', 'headRepository'],
  ['--base-repository', 'baseRepository'],
  ['--pr-number', 'prNumber'],
]);

function parseArgs(argv) {
  const args = { root: '.', expected: {}, requireSubjects: [] };
  for (let i = 0; i < argv.length; i += 1) {
    const arg = argv[i];
    const next = () => {
      i += 1;
      if (i >= argv.length) throw new Error(`${arg} requires a value`);
      return argv[i];
    };
    if (arg === '--provenance') args.provenancePath = next();
    else if (arg === '--root') args.root = next();
    else if (arg === '--require-subject') args.requireSubjects.push(next());
    else if (expectedFlagMap.has(arg)) args.expected[expectedFlagMap.get(arg)] = next();
    else if (arg === '--help' || arg === '-h') args.help = true;
    else throw new Error(`Unknown argument: ${arg}`);
  }
  return args;
}

function printHelp() {
  console.log(`Usage: node scripts/ci/validate-artifact-provenance.mjs --provenance <file> [--root <dir>] [expected flags] [--require-subject <path> ...]`);
}

try {
  const args = parseArgs(process.argv.slice(2));
  if (args.help) {
    printHelp();
    process.exit(0);
  }
  if (!args.provenancePath) throw new Error('--provenance is required');
  const provenance = JSON.parse(fs.readFileSync(args.provenancePath, 'utf8'));
  const errors = validateArtifactProvenance({
    provenance,
    root: args.root,
    expected: args.expected,
    requireSubjects: args.requireSubjects,
  });
  if (errors.length) {
    for (const error of errors) {
      console.error(`::error::${error}`);
    }
    process.exit(1);
  }
  console.log(`Validated artifact provenance: ${args.provenancePath}`);
} catch (error) {
  console.error(`validate-artifact-provenance: ${error instanceof Error ? error.message : String(error)}`);
  process.exit(1);
}
