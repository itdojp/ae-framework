#!/usr/bin/env node

import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { fileURLToPath } from 'node:url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

const DEFAULT_ROOT = path.resolve(__dirname, '..', '..');
const DEFAULT_CATALOG = path.join('docs', 'reference', 'CONTRACT-CATALOG.md');
const DEFAULT_SCHEMA_DIR = 'schema';

function parseArgs(argv = process.argv) {
  const options = {
    rootDir: DEFAULT_ROOT,
    catalogPath: DEFAULT_CATALOG,
    schemaDir: DEFAULT_SCHEMA_DIR,
    help: false,
  };

  for (let index = 2; index < argv.length; index += 1) {
    const arg = argv[index];
    const next = argv[index + 1];
    if (arg === '--help' || arg === '-h') {
      options.help = true;
      continue;
    }
    if (arg === '--root') {
      if (!next || next.startsWith('-')) {
        throw new Error('missing value for --root');
      }
      options.rootDir = path.resolve(next);
      index += 1;
      continue;
    }
    if (arg.startsWith('--root=')) {
      options.rootDir = path.resolve(arg.slice('--root='.length));
      continue;
    }
    if (arg === '--catalog') {
      if (!next || next.startsWith('-')) {
        throw new Error('missing value for --catalog');
      }
      options.catalogPath = next;
      index += 1;
      continue;
    }
    if (arg.startsWith('--catalog=')) {
      options.catalogPath = arg.slice('--catalog='.length);
      continue;
    }
    if (arg === '--schema-dir') {
      if (!next || next.startsWith('-')) {
        throw new Error('missing value for --schema-dir');
      }
      options.schemaDir = next;
      index += 1;
      continue;
    }
    if (arg.startsWith('--schema-dir=')) {
      options.schemaDir = arg.slice('--schema-dir='.length);
      continue;
    }
    throw new Error(`unknown option: ${arg}`);
  }

  return options;
}

function listSchemas(rootDir, schemaDir) {
  const absoluteSchemaDir = path.resolve(rootDir, schemaDir);
  if (!fs.existsSync(absoluteSchemaDir)) {
    return [];
  }
  return fs
    .readdirSync(absoluteSchemaDir)
    .filter((entry) => entry.endsWith('.schema.json'))
    .sort((left, right) => left.localeCompare(right))
    .map((entry) => path.posix.join(schemaDir.replace(/\\/g, '/'), entry));
}

function checkCatalogCoverage({ rootDir, catalogPath, schemaDir }) {
  const schemaPaths = listSchemas(rootDir, schemaDir);
  const absoluteCatalogPath = path.resolve(rootDir, catalogPath);
  if (!fs.existsSync(absoluteCatalogPath)) {
    return {
      ok: false,
      schemaPaths,
      missingInCatalog: schemaPaths,
      catalogPath: absoluteCatalogPath,
      message: 'catalog file not found',
    };
  }
  const markdown = fs.readFileSync(absoluteCatalogPath, 'utf8');
  const missingInCatalog = schemaPaths.filter((schemaPath) => !markdown.includes(`\`${schemaPath}\``));
  return {
    ok: missingInCatalog.length === 0,
    schemaPaths,
    missingInCatalog,
    catalogPath: absoluteCatalogPath,
    message: missingInCatalog.length === 0
      ? 'all schema files are listed in contract catalog'
      : 'some schema files are missing in contract catalog',
  };
}

function printHelp() {
  process.stdout.write(`Check coverage between schema files and docs/reference/CONTRACT-CATALOG.md.

Usage:
  node scripts/docs/check-contract-catalog-coverage.mjs [options]

Options:
  --root <path>         Repository root (default: current repository root)
  --catalog <path>      Contract catalog markdown path (default: docs/reference/CONTRACT-CATALOG.md)
  --schema-dir <path>   Schema directory (default: schema)
  --help, -h            Show this help
`);
}

export function run(argv = process.argv) {
  const options = parseArgs(argv);
  if (options.help) {
    printHelp();
    return 0;
  }

  const result = checkCatalogCoverage(options);
  if (!result.ok) {
    process.stderr.write(`[contract-catalog] FAILED: ${result.message}\n`);
    process.stderr.write(`[contract-catalog] catalog: ${result.catalogPath}\n`);
    for (const missing of result.missingInCatalog) {
      process.stderr.write(`[contract-catalog] missing: ${missing}\n`);
    }
    return 1;
  }

  process.stdout.write(`[contract-catalog] OK: ${result.schemaPaths.length} schema files are listed.\n`);
  return 0;
}

export { checkCatalogCoverage, listSchemas, parseArgs };

if (process.argv[1] && path.resolve(process.argv[1]) === __filename) {
  process.exit(run(process.argv));
}
