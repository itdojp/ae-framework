#!/usr/bin/env node
import { readFileSync, readdirSync, statSync } from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import yaml from 'yaml';

const repoRoot = process.cwd();
const schemaPath = path.join(repoRoot, 'schema', 'assurance-profile.schema.json');
const CURRENT_REQUIRED_CHECK_CONTEXTS = new Set(['verify-lite', 'policy-gate', 'gate']);

function usage() {
  process.stdout.write(`Usage: node scripts/profiles/validate-profiles.mjs [profile-file ...]\n\n` +
    `When no files are provided, all .json/.yaml/.yml files in profiles/ are validated.\n`);
}

function collectDefaultProfileFiles() {
  const profilesDir = path.join(repoRoot, 'profiles');
  let entries;
  try {
    entries = readdirSync(profilesDir, { withFileTypes: true });
  } catch (error) {
    throw new Error(`profiles/ directory is not readable: ${error instanceof Error ? error.message : String(error)}`);
  }
  return entries
    .filter((entry) => entry.isFile() && /\.(json|ya?ml)$/u.test(entry.name))
    .map((entry) => path.join('profiles', entry.name))
    .sort();
}

function loadProfile(filePath) {
  const resolved = path.resolve(repoRoot, filePath);
  const raw = readFileSync(resolved, 'utf8');
  const extension = path.extname(filePath).toLowerCase();
  if (extension === '.yaml' || extension === '.yml') {
    return yaml.parse(raw);
  }
  return JSON.parse(raw);
}

function ensureExistingSchemaRefs(profile, filePath) {
  const refs = profile?.deployment?.artifactSchemas;
  if (!Array.isArray(refs)) {
    return [`${filePath}: deployment.artifactSchemas must be present for deploy-time profiles`];
  }
  const errors = [];
  for (const [index, ref] of refs.entries()) {
    const target = typeof ref?.path === 'string' ? ref.path : '';
    if (!target) {
      errors.push(`${filePath}: deployment.artifactSchemas[${index}].path is required`);
      continue;
    }
    const resolved = path.resolve(repoRoot, target);
    try {
      const stat = statSync(resolved);
      if (!stat.isFile()) {
        errors.push(`${filePath}: schema reference is not a file: ${target}`);
      }
    } catch {
      errors.push(`${filePath}: schema reference does not exist: ${target}`);
    }
  }
  return errors;
}

function validateDeployProfileSemantics(profile, filePath) {
  const errors = [];
  if (!profile || typeof profile !== 'object') {
    return [`${filePath}: profile must parse to an object`];
  }
  if (!profile.deployment || typeof profile.deployment !== 'object') {
    errors.push(`${filePath}: deployment object is required for deploy-time profiles`);
    return errors;
  }
  if (profile.deployment.tier !== 'custom' && profile.deployment.tier !== profile.profileId) {
    errors.push(`${filePath}: deployment.tier must match profileId (${profile.profileId})`);
  }
  const requiredChecks = profile.deployment.requiredChecks;
  if (Array.isArray(requiredChecks)) {
    for (const checkContext of requiredChecks) {
      if (!CURRENT_REQUIRED_CHECK_CONTEXTS.has(checkContext)) {
        errors.push(
          `${filePath}: deployment.requiredChecks contains "${checkContext}", `
          + `which is not one of the current branch-protection check contexts: `
          + `${Array.from(CURRENT_REQUIRED_CHECK_CONTEXTS).join(', ')}`
        );
      }
    }
  }
  errors.push(...ensureExistingSchemaRefs(profile, filePath));
  return errors;
}

function main(argv = process.argv.slice(2)) {
  if (argv.includes('--help') || argv.includes('-h')) {
    usage();
    return;
  }

  const profileFiles = argv.length > 0 ? argv : collectDefaultProfileFiles();
  if (profileFiles.length === 0) {
    throw new Error('No profile files found to validate');
  }

  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  const schema = JSON.parse(readFileSync(schemaPath, 'utf8'));
  const validate = ajv.compile(schema);
  const failures = [];

  for (const filePath of profileFiles) {
    const profile = loadProfile(filePath);
    const ok = validate(profile);
    if (!ok) {
      failures.push({ filePath, errors: validate.errors ?? [] });
      continue;
    }
    const semanticErrors = validateDeployProfileSemantics(profile, filePath);
    if (semanticErrors.length > 0) {
      failures.push({ filePath, errors: semanticErrors });
    }
  }

  if (failures.length > 0) {
    process.stderr.write('Profile validation failed:\n');
    for (const failure of failures) {
      process.stderr.write(`- ${failure.filePath}\n`);
      for (const error of failure.errors) {
        process.stderr.write(`  ${typeof error === 'string' ? error : JSON.stringify(error)}\n`);
      }
    }
    process.exitCode = 1;
    return;
  }

  process.stdout.write(`Validated ${profileFiles.length} deploy-time assurance profile(s): ${profileFiles.join(', ')}\n`);
}

try {
  main();
} catch (error) {
  process.stderr.write(`${error instanceof Error ? error.message : String(error)}\n`);
  process.exitCode = 1;
}
