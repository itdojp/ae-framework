#!/usr/bin/env node

import { readFileSync } from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { fileURLToPath } from 'node:url';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import { validatePublicationEvidenceSemantics } from './publication-evidence-contract.mjs';

const DEFAULT_MANIFEST = 'docs/operate/publication-evidence.json';
const DEFAULT_SCHEMA = 'schema/publication-evidence-v1.schema.json';

function parseArgs(argv) {
  const positional = [];
  for (const arg of argv.slice(2)) {
    if (arg === '--help' || arg === '-h') {
      return { help: true };
    }
    positional.push(arg);
  }
  if (positional.length > 2) {
    throw new Error('usage: validate-publication-evidence.mjs [manifest] [schema]');
  }
  return {
    help: false,
    manifestPath: positional[0] ?? DEFAULT_MANIFEST,
    schemaPath: positional[1] ?? DEFAULT_SCHEMA,
  };
}

function formatErrors(errors = []) {
  return errors
    .map((entry) => `${entry.instancePath || '/'}: ${entry.message || entry.keyword || 'invalid'}`)
    .join('\n');
}

export function validatePublicationEvidenceFiles({ manifestPath, schemaPath, cwd = process.cwd() }) {
  const resolvedManifest = path.resolve(cwd, manifestPath);
  const resolvedSchema = path.resolve(cwd, schemaPath);
  const manifest = JSON.parse(readFileSync(resolvedManifest, 'utf8'));
  const schema = JSON.parse(readFileSync(resolvedSchema, 'utf8'));
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  const validateSchema = ajv.compile(schema);
  const schemaValid = validateSchema(manifest);
  const semanticErrors = schemaValid ? validatePublicationEvidenceSemantics(manifest) : [];
  return {
    valid: schemaValid && semanticErrors.length === 0,
    manifest,
    manifestPath: path.relative(cwd, resolvedManifest),
    schemaPath: path.relative(cwd, resolvedSchema),
    schemaErrors: validateSchema.errors ?? [],
    semanticErrors,
  };
}

export function run(argv = process.argv) {
  const options = parseArgs(argv);
  if (options.help) {
    process.stdout.write('Usage: node scripts/release/validate-publication-evidence.mjs [manifest] [schema]\n');
    return 0;
  }
  const result = validatePublicationEvidenceFiles(options);
  if (!result.valid) {
    const sections = [];
    if (result.schemaErrors.length > 0) {
      sections.push(`Schema errors:\n${formatErrors(result.schemaErrors)}`);
    }
    if (result.semanticErrors.length > 0) {
      sections.push(`Semantic errors:\n${formatErrors(result.semanticErrors)}`);
    }
    process.stderr.write(`Publication evidence validation: FAILED\n${sections.join('\n')}\n`);
    return 1;
  }
  const stateSummary = Object.entries(result.manifest.surfaces)
    .map(([name, surface]) => `${name}=${surface.state}`)
    .join(', ');
  process.stdout.write('Publication evidence validation: OK\n');
  process.stdout.write(`- manifest: ${result.manifestPath}\n`);
  process.stdout.write(`- schema: ${result.schemaPath}\n`);
  process.stdout.write(`- states: ${stateSummary}\n`);
  return 0;
}

export function isExecutedAsMain(metaUrl, argvPath = process.argv[1]) {
  if (!argvPath) {
    return false;
  }
  return path.resolve(fileURLToPath(metaUrl)) === path.resolve(argvPath);
}

if (isExecutedAsMain(import.meta.url)) {
  try {
    process.exitCode = run();
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    process.stderr.write(`Publication evidence validation: FAILED\n${message}\n`);
    process.exitCode = 1;
  }
}
