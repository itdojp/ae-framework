#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';

const DEFAULT_ALLOWED_DIR = path.join('artifacts', 'observability', 'runtime-self-heal-inputs');
const DEFAULT_OUTPUT = path.join('artifacts', 'observability', 'runtime-self-heal-trace-bundle.json');
const TRACE_BUNDLE_SCHEMA = path.join('schema', 'trace-bundle.schema.json');

const usage = () => {
  process.stderr.write(`Usage: node scripts/ci/validate-runtime-self-heal-trace-bundle.mjs --input <path> [--allowed-dir <dir>] [--output <path>]\n`);
};

const parseArgs = (argv) => {
  const options = {
    allowedDir: DEFAULT_ALLOWED_DIR,
    output: DEFAULT_OUTPUT,
  };
  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    const next = argv[index + 1];
    if (arg === '--input' && next) {
      options.input = next;
      index += 1;
    } else if (arg === '--allowed-dir' && next) {
      options.allowedDir = next;
      index += 1;
    } else if (arg === '--output' && next) {
      options.output = next;
      index += 1;
    } else if (arg === '--help') {
      usage();
      process.exit(0);
    } else {
      throw new Error(`Unknown or incomplete argument: ${arg}`);
    }
  }
  if (!options.input) {
    throw new Error('--input is required');
  }
  return options;
};

const pathSegments = (value) => value.split(/[\\/]+/u).filter(Boolean);

const rejectUnsafeRelativePath = (name, value) => {
  if (/[\u0000-\u001f\u007f]/u.test(value)) {
    throw new Error(`${name} must not contain control characters`);
  }
  if (path.isAbsolute(value)) {
    throw new Error(`${name} must be repository-relative`);
  }
  if (/^[a-zA-Z]:[\\/]/u.test(value) || value.startsWith('\\\\') || value.startsWith('//')) {
    throw new Error(`${name} must be repository-relative`);
  }
  if (value.includes('\\')) {
    throw new Error(`${name} must use POSIX-style separators`);
  }
  const segments = pathSegments(value);
  if (segments.length === 0) {
    throw new Error(`${name} must not be empty`);
  }
  for (const segment of segments) {
    if (segment === '..') {
      throw new Error(`${name} must not contain parent traversal`);
    }
    if (segment === '.git') {
      throw new Error(`${name} must not reference repository metadata`);
    }
  }
};

const ensureUnder = (name, candidate, parent) => {
  const relative = path.relative(parent, candidate);
  if (relative === '' || (!relative.startsWith('..') && !path.isAbsolute(relative))) {
    return;
  }
  throw new Error(`${name} must be under ${path.relative(process.cwd(), parent) || parent}`);
};

const assertNoSymlinkInPath = (absolutePath, stopAt, name = 'trace_bundle') => {
  const root = path.resolve(stopAt);
  const target = path.resolve(absolutePath);
  ensureUnder(name, target, root);
  const rootStat = fs.lstatSync(root);
  if (rootStat.isSymbolicLink()) {
    throw new Error(`${name} must not traverse symlinks: ${path.relative(process.cwd(), root)}`);
  }
  const relative = path.relative(root, target);
  let current = root;
  for (const segment of pathSegments(relative)) {
    current = path.join(current, segment);
    const stat = fs.lstatSync(current);
    if (stat.isSymbolicLink()) {
      throw new Error(`${name} must not traverse symlinks: ${path.relative(process.cwd(), current)}`);
    }
  }
};

const readJson = (file) => JSON.parse(fs.readFileSync(file, 'utf8'));

const validateBundle = (repoRoot, inputPath) => {
  const schema = readJson(path.join(repoRoot, TRACE_BUNDLE_SCHEMA));
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  const validate = ajv.compile(schema);
  const data = readJson(inputPath);
  if (!validate(data)) {
    const details = (validate.errors ?? [])
      .slice(0, 5)
      .map((error) => `${error.instancePath || '/'} ${error.message ?? ''}`.trim())
      .join('; ');
    throw new Error(`trace_bundle does not match ae-trace-bundle/v1 schema${details ? `: ${details}` : ''}`);
  }
};

const main = () => {
  const options = parseArgs(process.argv.slice(2));
  const repoRoot = process.cwd();

  rejectUnsafeRelativePath('allowed-dir', options.allowedDir);
  rejectUnsafeRelativePath('input', options.input);
  rejectUnsafeRelativePath('output', options.output);

  const allowedDir = path.resolve(repoRoot, options.allowedDir);
  const input = path.resolve(repoRoot, options.input);
  const output = path.resolve(repoRoot, options.output);
  const outputRoot = path.resolve(repoRoot, 'artifacts', 'observability');

  ensureUnder('allowed-dir', allowedDir, repoRoot);
  ensureUnder('input', input, allowedDir);
  ensureUnder('output', output, outputRoot);

  if (!fs.existsSync(input)) {
    throw new Error(`trace_bundle not found: ${options.input}`);
  }
  assertNoSymlinkInPath(allowedDir, repoRoot, 'allowed-dir');
  assertNoSymlinkInPath(input, allowedDir);
  const stat = fs.statSync(input);
  if (!stat.isFile()) {
    throw new Error(`trace_bundle must be a regular file: ${options.input}`);
  }

  validateBundle(repoRoot, input);

  fs.mkdirSync(path.dirname(output), { recursive: true });
  fs.copyFileSync(input, output);
  process.stdout.write(`Validated runtime self-heal trace bundle: ${options.input} -> ${options.output}\n`);
};

try {
  main();
} catch (error) {
  const message = error instanceof Error ? error.message : String(error);
  process.stderr.write(`::error::${message}\n`);
  process.exit(1);
}
