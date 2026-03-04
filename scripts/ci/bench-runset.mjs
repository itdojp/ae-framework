#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';

function printUsage() {
  process.stdout.write(`Usage: node scripts/ci/bench-runset.mjs [options] <bench.json ...>

Options:
  --out <path>                  write comma-separated runset to file
  --min-runs <number>           minimum required runs (default: 2)
  --schema-version <value>      required schemaVersion (default: benchmark-report/v1)
  --absolute                    output absolute paths
  --help                        show this message
`);
}

function parsePositiveInt(value, label) {
  const normalized = String(value || '').trim();
  if (!/^[1-9]\d*$/.test(normalized)) {
    throw new Error(`${label} must be a positive integer`);
  }
  return Number(normalized);
}

function parseArgs(argv) {
  const options = {
    outPath: '',
    minRuns: 2,
    schemaVersion: 'benchmark-report/v1',
    absolute: false,
    files: [],
  };

  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--help' || arg === '-h') {
      printUsage();
      process.exit(0);
    }
    if (arg === '--out') {
      const next = argv[index + 1];
      if (!next) throw new Error('--out requires a value');
      options.outPath = path.resolve(next);
      index += 1;
      continue;
    }
    if (arg === '--min-runs') {
      const next = argv[index + 1];
      if (!next) throw new Error('--min-runs requires a value');
      options.minRuns = parsePositiveInt(next, '--min-runs');
      index += 1;
      continue;
    }
    if (arg === '--schema-version') {
      const next = argv[index + 1];
      if (!next) throw new Error('--schema-version requires a value');
      options.schemaVersion = String(next).trim();
      index += 1;
      continue;
    }
    if (arg === '--absolute') {
      options.absolute = true;
      continue;
    }
    if (arg.startsWith('--')) {
      throw new Error(`Unknown argument: ${arg}`);
    }
    options.files.push(path.resolve(arg));
  }

  if (!options.schemaVersion) {
    throw new Error('--schema-version must not be empty');
  }

  return options;
}

function readJson(filePath) {
  const raw = fs.readFileSync(filePath, 'utf8');
  return JSON.parse(raw);
}

function normalizeAndValidateFiles(files, requiredSchemaVersion) {
  const dedupedSorted = Array.from(new Set(files)).sort((left, right) => left.localeCompare(right));
  if (dedupedSorted.length === 0) {
    throw new Error('at least one bench report path is required');
  }

  for (const filePath of dedupedSorted) {
    if (!fs.existsSync(filePath)) {
      throw new Error(`file not found: ${filePath}`);
    }
    const report = readJson(filePath);
    if (report?.schemaVersion !== requiredSchemaVersion) {
      throw new Error(
        `schemaVersion mismatch at ${filePath}: expected ${requiredSchemaVersion}, got ${String(report?.schemaVersion || '')}`,
      );
    }
    if (!Array.isArray(report.summary) || report.summary.length === 0) {
      throw new Error(`${filePath}: summary must be a non-empty array`);
    }
  }

  return dedupedSorted;
}

function toOutputPath(filePath, absolute) {
  return absolute ? filePath : path.relative(process.cwd(), filePath);
}

function main() {
  const options = parseArgs(process.argv.slice(2));
  const normalizedFiles = normalizeAndValidateFiles(options.files, options.schemaVersion);
  if (normalizedFiles.length < options.minRuns) {
    throw new Error(`insufficient run files: required >= ${options.minRuns}, got ${normalizedFiles.length}`);
  }

  const output = normalizedFiles
    .map((filePath) => toOutputPath(filePath, options.absolute))
    .join(',');

  if (options.outPath) {
    fs.mkdirSync(path.dirname(options.outPath), { recursive: true });
    fs.writeFileSync(options.outPath, `${output}\n`, 'utf8');
  }
  process.stdout.write(`${output}\n`);
}

try {
  main();
} catch (error) {
  const message = error instanceof Error ? error.message : String(error);
  process.stderr.write(`[bench-runset] ${message}\n`);
  process.exitCode = 1;
}
