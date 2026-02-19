#!/usr/bin/env node

import { readFileSync, readdirSync } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const DEFAULT_REPO_ROOT = path.resolve(__dirname, '..', '..');

export const ALLOWED_SCHEMA_ID_PREFIXES = [
  'https://ae-framework/schema/',
  'https://itdojp.github.io/ae-framework/schema/',
];

function parseArgs(argv) {
  let rootDir = DEFAULT_REPO_ROOT;
  let format = 'text';

  for (const arg of argv.slice(2)) {
    if (arg.startsWith('--root=')) {
      rootDir = path.resolve(arg.slice('--root='.length));
      continue;
    }
    if (arg.startsWith('--format=')) {
      const value = arg.slice('--format='.length);
      if (value === 'text' || value === 'json') {
        format = value;
      }
    }
  }

  return { rootDir, format };
}

function createViolation(file, type, reason, id) {
  const violation = { file, type, reason };
  if (typeof id === 'string') {
    violation.id = id;
  }
  return violation;
}

function countViolationsByType(violations) {
  const counts = {};
  for (const violation of violations) {
    counts[violation.type] = (counts[violation.type] ?? 0) + 1;
  }
  return counts;
}

export function scanSchemaIdPolicy(rootDir) {
  const resolvedRoot = path.resolve(rootDir);
  const schemaDir = path.resolve(resolvedRoot, 'schema');
  let schemaFiles;

  try {
    schemaFiles = readdirSync(schemaDir, { withFileTypes: true })
      .filter((entry) => entry.isFile() && entry.name.endsWith('.schema.json'))
      .map((entry) => entry.name)
      .sort((a, b) => a.localeCompare(b));
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    const failures = [
      createViolation(
        path.relative(resolvedRoot, schemaDir) || 'schema',
        'schema_dir_read_error',
        `failed to read schema directory: ${message}`,
      ),
    ];
    return {
      rootDir: resolvedRoot,
      schemaDir,
      scannedFiles: 0,
      compliantFiles: 0,
      violatingFiles: ['schema'],
      violations: failures,
      violationCounts: countViolationsByType(failures),
    };
  }

  const violations = [];
  const violatingFiles = new Set();

  for (const fileName of schemaFiles) {
    const relativeFile = path.posix.join('schema', fileName);
    const filePath = path.resolve(schemaDir, fileName);
    let parsed;

    try {
      parsed = JSON.parse(readFileSync(filePath, 'utf8'));
    } catch (error) {
      const message = error instanceof Error ? error.message : String(error);
      violations.push(createViolation(relativeFile, 'invalid_json', `invalid JSON: ${message}`));
      violatingFiles.add(relativeFile);
      continue;
    }

    const rawId = parsed?.$id;
    if (typeof rawId !== 'string' || rawId.trim().length === 0) {
      violations.push(createViolation(relativeFile, 'missing_id', 'missing `$id` property'));
      violatingFiles.add(relativeFile);
      continue;
    }

    const id = rawId.trim();
    const matchedPrefix = ALLOWED_SCHEMA_ID_PREFIXES.find((prefix) => id.startsWith(prefix));
    if (!matchedPrefix) {
      violations.push(
        createViolation(
          relativeFile,
          'invalid_prefix',
          `non-allowed prefix (allowed: ${ALLOWED_SCHEMA_ID_PREFIXES.join(', ')})`,
          id,
        ),
      );
      violatingFiles.add(relativeFile);
      continue;
    }

    const idFileName = id.slice(matchedPrefix.length);
    if (idFileName !== fileName) {
      violations.push(
        createViolation(
          relativeFile,
          'filename_mismatch',
          `filename mismatch (expected: ${fileName}, actual: ${idFileName || '(empty)'})`,
          id,
        ),
      );
      violatingFiles.add(relativeFile);
    }
  }

  return {
    rootDir: resolvedRoot,
    schemaDir,
    scannedFiles: schemaFiles.length,
    compliantFiles: schemaFiles.length - violatingFiles.size,
    violatingFiles: [...violatingFiles].sort((a, b) => a.localeCompare(b)),
    violations,
    violationCounts: countViolationsByType(violations),
  };
}

function renderText(result, exitCode) {
  const lines = [];
  lines.push('Schema $id policy check');
  lines.push(`- root: ${result.rootDir}`);
  lines.push(`- schemaDir: ${result.schemaDir}`);
  lines.push(`- scannedFiles: ${result.scannedFiles}`);
  lines.push(`- compliantFiles: ${result.compliantFiles}`);
  lines.push(`- violatingFiles: ${result.violatingFiles.length}`);
  lines.push(`- violations: ${result.violations.length}`);

  const breakdownEntries = Object.entries(result.violationCounts)
    .sort(([left], [right]) => left.localeCompare(right));
  if (breakdownEntries.length > 0) {
    lines.push('- breakdown:');
    for (const [type, count] of breakdownEntries) {
      lines.push(`  - ${type}: ${count}`);
    }
  }

  if (result.violations.length > 0) {
    lines.push('');
    lines.push('Violations:');
    for (const violation of result.violations) {
      const idText = typeof violation.id === 'string' ? ` | id: ${violation.id}` : '';
      lines.push(`- ${violation.file} [${violation.type}] ${violation.reason}${idText}`);
    }
  }

  lines.push(`- exitCode: ${exitCode}`);
  return `${lines.join('\n')}\n`;
}

export function runSchemaIdPolicyCheck(argv = process.argv) {
  const options = parseArgs(argv);
  const result = scanSchemaIdPolicy(options.rootDir);
  const exitCode = result.violations.length > 0 ? 1 : 0;
  if (options.format === 'json') {
    process.stdout.write(JSON.stringify({
      root: result.rootDir,
      schemaDir: result.schemaDir,
      scannedFiles: result.scannedFiles,
      compliantFiles: result.compliantFiles,
      violatingFiles: result.violatingFiles,
      violations: result.violations,
      violationCounts: result.violationCounts,
      exitCode,
    }, null, 2));
    process.stdout.write('\n');
  } else {
    process.stdout.write(renderText(result, exitCode));
  }
  return { ...result, exitCode, options };
}

export function isExecutedAsMain(metaUrl, argvPath = process.argv[1]) {
  if (!argvPath || typeof argvPath !== 'string') {
    return false;
  }
  try {
    const modulePath = path.resolve(fileURLToPath(metaUrl));
    const entryPath = path.resolve(argvPath);
    return modulePath === entryPath;
  } catch {
    return false;
  }
}

if (isExecutedAsMain(import.meta.url, process.argv[1])) {
  const result = runSchemaIdPolicyCheck(process.argv);
  process.exit(result.exitCode);
}
