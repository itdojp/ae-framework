import fs from 'node:fs';
import { spawnSync } from 'node:child_process';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

import { Command } from 'commander';

import { safeExit } from '../utils/safe-exit.js';

const __dirname = path.dirname(fileURLToPath(import.meta.url));

const DISCOVERY_SCRIPT_PATH = ['scripts', 'discovery-pack', 'validate.mjs'];
const DISCOVERY_SCHEMA_PATH = ['schema', 'discovery-pack-v1.schema.json'];

const hasDiscoveryAssets = (candidateRoot: string) =>
  fs.existsSync(path.join(candidateRoot, 'package.json')) &&
  fs.existsSync(path.join(candidateRoot, ...DISCOVERY_SCRIPT_PATH)) &&
  fs.existsSync(path.join(candidateRoot, ...DISCOVERY_SCHEMA_PATH));

const enumerateCandidateRoots = (startPath: string) => {
  const candidates: string[] = [];
  let current = path.resolve(startPath);
  while (!candidates.includes(current)) {
    candidates.push(current);
    const parent = path.dirname(current);
    if (parent === current) {
      break;
    }
    current = parent;
  }
  return candidates;
};

export const resolveDiscoveryToolPaths = (
  cwd = process.cwd(),
  moduleDir = __dirname,
) => {
  const candidates = [
    ...enumerateCandidateRoots(cwd),
    ...enumerateCandidateRoots(moduleDir),
  ];
  const repoRoot = candidates.find(hasDiscoveryAssets);
  if (!repoRoot) {
    throw new Error(
      'Could not locate discovery-pack validate assets (package.json, scripts/discovery-pack/validate.mjs, schema/discovery-pack-v1.schema.json)',
    );
  }
  return {
    repoRoot,
    discoveryValidateScript: path.join(repoRoot, ...DISCOVERY_SCRIPT_PATH),
    discoverySchemaPath: path.join(repoRoot, ...DISCOVERY_SCHEMA_PATH),
  };
};

// Keep this parser aligned with scripts/discovery-pack/lib.mjs#splitSourcePatterns.
const splitBraceAware = (value: string) => {
  const chunks: string[] = [];
  let buffer = '';
  let braceDepth = 0;
  for (const char of value) {
    if (char === '{') {
      braceDepth += 1;
      buffer += char;
      continue;
    }
    if (char === '}') {
      braceDepth = Math.max(0, braceDepth - 1);
      buffer += char;
      continue;
    }
    if (char === ',' && braceDepth === 0) {
      chunks.push(buffer);
      buffer = '';
      continue;
    }
    buffer += char;
  }
  chunks.push(buffer);
  return chunks;
};

const collectSourceValues = (value: string, previous: string[] = []) =>
  previous.concat(
    splitBraceAware(value)
      .map((entry) => entry.trim())
      .filter(Boolean),
  );

const collectListValues = (value: string, previous: string[] = []) =>
  previous.concat(
    value
      .split(',')
      .map((entry) => entry.trim())
      .filter(Boolean),
  );

const runNodeScript = (scriptPath: string, args: string[]) => {
  const result = spawnSync(process.execPath, [scriptPath, ...args], {
    cwd: process.cwd(),
    encoding: 'utf8',
    env: process.env,
  });

  if (result.stdout) {
    process.stdout.write(result.stdout);
  }
  if (result.stderr) {
    process.stderr.write(result.stderr);
  }
  if (result.error) {
    throw result.error;
  }
  safeExit(result.status ?? 1);
};

export const createDiscoveryCommand = () => {
  const discovery = new Command('discovery').description('Discovery Pack commands');

  discovery
    .command('validate')
    .description('Validate Discovery Pack inputs')
    .option('--sources <glob>', 'Source glob (repeatable, comma-separated supported)', collectSourceValues, [])
    .option('--format <format>', 'json | md | both', 'both')
    .option('--output-dir <dir>', 'Output directory', 'artifacts/discovery-pack')
    .option('--strict-approved', 'Fail when approved elements depend on non-approved elements')
    .option(
      '--fail-on <rule>',
      'Repeatable fail-on rule: blocking-open-questions, orphan-approved-requirements, orphan-approved-business-use-cases',
      collectListValues,
      [],
    )
    .action((options) => {
      const { discoverySchemaPath, discoveryValidateScript } = resolveDiscoveryToolPaths();
      const args = [
        '--schema',
        discoverySchemaPath,
        '--format',
        options.format,
        '--output-dir',
        options.outputDir,
      ];
      for (const source of options.sources as string[]) {
        args.push('--sources', source);
      }
      if (options.strictApproved) {
        args.push('--strict-approved');
      }
      for (const rule of options.failOn as string[]) {
        args.push('--fail-on', rule);
      }
      runNodeScript(discoveryValidateScript, args);
    });

  return discovery;
};
