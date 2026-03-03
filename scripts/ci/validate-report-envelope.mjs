#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import { toLegacyReportEnvelope } from '../trace/lib/report-envelope-compat.mjs';

const envelopeSchemaPath = 'schema/envelope.schema.json';
const reportSchemaPath = 'schema/report-envelope.schema.json';
const defaultSchema = fs.existsSync(envelopeSchemaPath) ? envelopeSchemaPath : reportSchemaPath;

function toBool(value) {
  if (value === undefined || value === null) return false;
  const normalized = String(value).trim().toLowerCase();
  return normalized === '1' || normalized === 'true' || normalized === 'yes' || normalized === 'on';
}

function parseArgs(argv = process.argv) {
  const positional = [];
  const options = {
    dualValidate: toBool(process.env.REPORT_ENVELOPE_DUAL_VALIDATE),
    legacySchemaPath: reportSchemaPath,
  };

  for (let index = 2; index < argv.length; index += 1) {
    const arg = argv[index];
    const next = argv[index + 1];

    if (arg === '--dual') {
      options.dualValidate = true;
      continue;
    }
    if (arg.startsWith('--dual=')) {
      options.dualValidate = toBool(arg.slice('--dual='.length));
      continue;
    }
    if (arg === '--legacy-schema') {
      if (!next || next.startsWith('-')) {
        throw new Error('missing value for --legacy-schema');
      }
      options.legacySchemaPath = next;
      index += 1;
      continue;
    }
    if (arg.startsWith('--legacy-schema=')) {
      options.legacySchemaPath = arg.slice('--legacy-schema='.length);
      continue;
    }
    positional.push(arg);
  }

  return {
    envelopePath: positional[0] ?? 'artifacts/report-envelope.json',
    schemaPath: positional[1] ?? defaultSchema,
    ...options,
  };
}

function readJson(filePath, label) {
  try {
    return JSON.parse(fs.readFileSync(filePath, 'utf8'));
  } catch (error) {
    console.error(`[report-envelope] failed to parse ${label} ${filePath}:`, error);
    process.exit(1);
  }
}

function validatePayload(payload, schemaPath, label) {
  if (!fs.existsSync(schemaPath)) {
    console.error(`[report-envelope] schema not found at ${schemaPath}`);
    process.exit(1);
  }

  const schema = readJson(schemaPath, 'schema');
  const ajv = new Ajv2020({ allErrors: true, strict: true });
  addFormats(ajv);
  const validate = ajv.compile(schema);

  if (!validate(payload)) {
    console.error(`[report-envelope] ${label} validation failed`);
    for (const err of validate.errors ?? []) {
      console.error(`  • ${err.instancePath || '/'} ${err.message}`);
    }
    process.exit(1);
  }

  console.log(`[report-envelope] ${label} validated against ${schemaPath}`);
}

const options = parseArgs(process.argv);
const resolvedEnvelope = path.resolve(options.envelopePath);
const resolvedSchema = path.resolve(options.schemaPath);
const resolvedLegacySchema = path.resolve(options.legacySchemaPath);

if (!fs.existsSync(resolvedEnvelope)) {
  console.warn(`[report-envelope] envelope not found at ${resolvedEnvelope}; skipping validation`);
  process.exit(0);
}

const envelope = readJson(resolvedEnvelope, 'envelope');
validatePayload(envelope, resolvedSchema, 'primary envelope');

if (options.dualValidate) {
  if (fs.existsSync(resolvedLegacySchema)) {
    const legacyEnvelope = toLegacyReportEnvelope(envelope);
    validatePayload(legacyEnvelope, resolvedLegacySchema, 'legacy envelope projection');
  } else {
    console.warn(`[report-envelope] legacy schema not found at ${resolvedLegacySchema}; dual validation skipped`);
  }
}
