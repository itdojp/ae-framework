import { spawnSync } from 'node:child_process';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

import { Command } from 'commander';

import { safeExit } from '../utils/safe-exit.js';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const repoRoot = path.resolve(__dirname, '..', '..');
const discoveryValidateScript = path.resolve(repoRoot, 'scripts', 'discovery-pack', 'validate.mjs');
const discoveryCompileScript = path.resolve(repoRoot, 'scripts', 'discovery-pack', 'compile.mjs');
const discoverySchemaPath = path.resolve(repoRoot, 'schema', 'discovery-pack-v1.schema.json');

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

  discovery
    .command('compile')
    .description('Compile Discovery Pack inputs into plan-spec or context-pack scaffold artifacts')
    .requiredOption('--target <target>', 'plan-spec | context-pack-scaffold')
    .option('--sources <glob>', 'Source glob (repeatable, comma-separated supported)', collectSourceValues, [])
    .option('--output-dir <dir>', 'Output directory', 'artifacts/discovery-pack')
    .option(
      '--include-status <status>',
      'Repeatable include-status value: hypothesis, reviewed, approved, rejected, deferred',
      collectListValues,
      [],
    )
    .action((options) => {
      const args = [
        '--target',
        options.target,
        '--schema',
        discoverySchemaPath,
        '--output-dir',
        options.outputDir,
      ];
      for (const source of options.sources as string[]) {
        args.push('--sources', source);
      }
      for (const status of options.includeStatus as string[]) {
        args.push('--include-status', status);
      }
      runNodeScript(discoveryCompileScript, args);
    });

  return discovery;
};
