#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import { buildArtifactProvenance } from './lib/artifact-provenance.mjs';

function parseArgs(argv) {
  const args = { subjects: [], root: '.' };
  for (let i = 0; i < argv.length; i += 1) {
    const arg = argv[i];
    const next = () => {
      i += 1;
      if (i >= argv.length) throw new Error(`${arg} requires a value`);
      return argv[i];
    };
    if (arg === '--output') args.output = next();
    else if (arg === '--artifact-name') args.artifactName = next();
    else if (arg === '--root') args.root = next();
    else if (arg === '--subject') args.subjects.push(next());
    else if (arg === '--help' || arg === '-h') args.help = true;
    else throw new Error(`Unknown argument: ${arg}`);
  }
  return args;
}

function printHelp() {
  console.log(`Usage: node scripts/ci/write-artifact-provenance.mjs --output <file> --artifact-name <name> [--root <dir>] --subject <path> [--subject <path> ...]`);
}

try {
  const args = parseArgs(process.argv.slice(2));
  if (args.help) {
    printHelp();
    process.exit(0);
  }
  if (!args.output) throw new Error('--output is required');
  const provenance = buildArtifactProvenance({
    artifactName: args.artifactName,
    root: args.root,
    subjects: args.subjects,
  });
  fs.mkdirSync(path.dirname(args.output), { recursive: true });
  fs.writeFileSync(args.output, `${JSON.stringify(provenance, null, 2)}\n`, 'utf8');
  console.log(`Wrote artifact provenance: ${args.output}`);
} catch (error) {
  console.error(`write-artifact-provenance: ${error instanceof Error ? error.message : String(error)}`);
  process.exit(1);
}
