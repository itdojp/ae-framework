#!/usr/bin/env node
import { existsSync, lstatSync, mkdirSync, readdirSync, readFileSync, realpathSync, statSync, writeFileSync } from 'node:fs';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { pathToFileURL } from 'node:url';

const SCRIPT_NAME = 'scripts/spec-verification/run-min-profile.mjs';
const DEFAULT_OUTPUT_JSON = 'artifacts/spec-kit-min/activation-summary.json';
const DEFAULT_OUTPUT_MD = 'artifacts/spec-kit-min/activation-summary.md';
const DEFAULT_PROPERTY_OUTPUT = 'artifacts/spec-kit-min/property-harness-summary.json';
const PASS = 'pass';
const FAIL = 'fail';
const WARNING = 'warning';
const SKIPPED = 'skipped';
const CHECK_IDS = new Set(['lint', 'types', 'fast', 'property-smoke', 'bdd-custom', 'property-custom']);

function toPosix(value) {
  return value.split(path.sep).join('/');
}

function repoRelative(filePath, root = process.cwd()) {
  const relative = path.relative(path.resolve(root), path.resolve(filePath));
  if (relative === '') return '.';
  return toPosix(relative && !relative.startsWith('..') ? relative : path.resolve(filePath));
}

function isPathWithin(parentPath, childPath) {
  const relative = path.relative(path.resolve(parentPath), path.resolve(childPath));
  return relative === '' || (relative !== '' && !relative.startsWith('..') && !path.isAbsolute(relative));
}

function lstatIfExists(filePath) {
  try {
    return lstatSync(filePath);
  } catch (error) {
    if (error?.code === 'ENOENT') return null;
    throw error;
  }
}

function realpathIfExists(filePath) {
  try {
    return realpathSync.native(filePath);
  } catch (error) {
    if (error?.code === 'ENOENT') return null;
    throw error;
  }
}

function nearestExistingAncestor(filePath) {
  let cursor = path.resolve(filePath);
  while (!lstatIfExists(cursor)) {
    const parent = path.dirname(cursor);
    if (parent === cursor) return null;
    cursor = parent;
  }
  return cursor;
}

function assertContainedPath(rootDir, filePath, label) {
  const root = path.resolve(rootDir);
  const resolved = path.resolve(root, filePath);
  if (!isPathWithin(root, resolved)) {
    throw new Error(`${label} must stay within the current workspace: ${filePath}`);
  }

  const ancestor = nearestExistingAncestor(resolved);
  if (!ancestor) return resolved;
  const realRoot = realpathSync.native(root);
  const realAncestor = realpathIfExists(ancestor);
  if (realAncestor && !isPathWithin(realRoot, realAncestor)) {
    throw new Error(`${label} resolves outside the current workspace: ${filePath}`);
  }
  return resolved;
}

function validateOptions(options) {
  if (options.help) return options;
  const root = process.cwd();
  assertContainedPath(root, options.profileRoot, '--profile-root');
  assertContainedPath(root, options.outputJson, '--output-json');
  assertContainedPath(root, options.outputMd, '--output-md');
  assertContainedPath(root, options.propertyOutput, '--property-output');
  return options;
}

function ensureOutputPath(filePath, label) {
  const resolved = assertContainedPath(process.cwd(), filePath, label);
  const stat = lstatIfExists(resolved);
  if (stat?.isSymbolicLink()) {
    throw new Error(`${label} must not be a symbolic link: ${filePath}`);
  }
  mkdirSync(path.dirname(resolved), { recursive: true });
  const statAfterMkdir = lstatIfExists(resolved);
  if (statAfterMkdir?.isSymbolicLink()) {
    throw new Error(`${label} must not be a symbolic link: ${filePath}`);
  }
  return resolved;
}

function shellQuote(value) {
  const text = String(value);
  if (/^[A-Za-z0-9_./:=@+-]+$/.test(text)) return text;
  return `'${text.replace(/'/g, `'"'"'`)}'`;
}

function parseArgs(argv = process.argv) {
  const options = {
    profileRoot: '.',
    outputJson: DEFAULT_OUTPUT_JSON,
    outputMd: DEFAULT_OUTPUT_MD,
    propertyOutput: DEFAULT_PROPERTY_OUTPUT,
    generatedAt: null,
    dryRun: false,
    noWrite: false,
    runCustomSuites: false,
    skippedChecks: new Set(),
    help: false,
  };
  const args = argv.slice(2);
  for (let index = 0; index < args.length; index += 1) {
    const arg = args[index];
    if (arg === '--' && index === 0) continue;
    if (arg === '--') break;
    if (arg === '--help' || arg === '-h') {
      options.help = true;
      continue;
    }
    if (arg === '--dry-run') {
      options.dryRun = true;
      continue;
    }
    if (arg === '--no-write') {
      options.noWrite = true;
      continue;
    }
    if (arg === '--run-custom-suites') {
      options.runCustomSuites = true;
      continue;
    }
    if (arg.startsWith('--skip=')) {
      addSkippedCheck(options, arg.slice('--skip='.length));
      continue;
    }
    const valueOptions = new Map([
      ['--profile-root', 'profileRoot'],
      ['--output-json', 'outputJson'],
      ['--output-md', 'outputMd'],
      ['--property-output', 'propertyOutput'],
      ['--generated-at', 'generatedAt'],
      ['--skip', 'skip'],
    ]);
    if (valueOptions.has(arg)) {
      const target = valueOptions.get(arg);
      const next = args[index + 1];
      if (!next || next.startsWith('--')) throw new Error(`${arg} requires a value`);
      if (target === 'skip') addSkippedCheck(options, next);
      else options[target] = next;
      index += 1;
      continue;
    }
    throw new Error(`Unknown argument: ${arg}`);
  }
  return validateOptions(options);
}

function addSkippedCheck(options, rawValue) {
  const checkId = String(rawValue || '').trim();
  if (!CHECK_IDS.has(checkId)) {
    throw new Error(`--skip must be one of ${[...CHECK_IDS].join(', ')}: ${checkId}`);
  }
  options.skippedChecks.add(checkId);
}

function renderHelp() {
  return [
    'Spec & Verification Kit minimum activation profile runner',
    '',
    'Usage:',
    `  node ${SCRIPT_NAME} [options]`,
    '',
    'Options:',
    '  --profile-root <path>       repository or generated sample root to inspect (default: .)',
    `  --output-json <path>        activation summary JSON (default: ${DEFAULT_OUTPUT_JSON})`,
    `  --output-md <path>          activation summary Markdown (default: ${DEFAULT_OUTPUT_MD})`,
    `  --property-output <path>    built-in property harness output path (default: ${DEFAULT_PROPERTY_OUTPUT})`,
    '  --generated-at <iso-date>   deterministic timestamp for fixtures/tests',
    '  --run-custom-suites         execute discovered BDD and property suites; otherwise report discovery only',
    '  --skip <check>              skip lint, types, fast, property-smoke, bdd-custom, or property-custom',
    '  --dry-run                  do not execute commands; emit planned command/artifact mapping',
    '  --no-write                 do not write summary artifacts',
    '  --help                     show this help',
  ].join('\n');
}

function listFilesRecursive(rootDir) {
  const resolved = path.resolve(rootDir);
  if (!existsSync(resolved) || !statSync(resolved).isDirectory()) return [];
  const entries = [];
  for (const name of readdirSync(resolved).sort()) {
    if (name === '.git' || name === 'node_modules' || name === 'dist' || name === 'coverage') continue;
    const child = path.join(resolved, name);
    const stat = lstatSync(child);
    if (stat.isSymbolicLink()) continue;
    if (stat.isDirectory()) entries.push(...listFilesRecursive(child));
    else if (stat.isFile()) entries.push(child);
  }
  return entries;
}

function readText(filePath) {
  try {
    return readFileSync(filePath, 'utf8');
  } catch {
    return '';
  }
}

function traceRefsFromContent(content) {
  const refs = new Set();
  for (const match of String(content || '').matchAll(/@trace:([A-Za-z0-9_.:-]+)/g)) {
    refs.add(match[1]);
  }
  return [...refs].sort();
}

function parseRequirementFile(filePath, profileRoot) {
  const content = readText(filePath);
  const refs = traceRefsFromContent(content);
  if (filePath.endsWith('.json')) {
    try {
      const payload = JSON.parse(content);
      const items = Array.isArray(payload) ? payload : Array.isArray(payload.requirements) ? payload.requirements : [payload];
      return items
        .map((item) => ({
          id: String(item.id || item.requirementId || '').trim(),
          title: String(item.title || item.summary || item.text || '').trim(),
          path: repoRelative(filePath, profileRoot),
        }))
        .filter((item) => item.id);
    } catch {
      return refs.map((id) => ({ id, title: 'Requirement trace marker', path: repoRelative(filePath, profileRoot) }));
    }
  }
  return refs.map((id) => ({ id, title: 'Requirement trace marker', path: repoRelative(filePath, profileRoot) }));
}

function discoverProfile(profileRoot) {
  const root = path.resolve(profileRoot);
  const files = listFilesRecursive(root);
  const isUnder = (filePath, segment) => toPosix(path.relative(root, filePath)).includes(segment);
  const featureFiles = files.filter((filePath) => isUnder(filePath, 'spec/bdd/') && filePath.endsWith('.feature'));
  const stepFiles = files.filter((filePath) => isUnder(filePath, 'spec/bdd/steps/') && /\.(?:cjs|mjs|js)$/.test(filePath));
  const propertyFiles = files.filter((filePath) => isUnder(filePath, 'tests/property/') && /\.(?:test|spec)\.(?:cjs|mjs|js|ts)$/.test(filePath));
  const requirementFiles = files.filter((filePath) => (
    isUnder(filePath, 'requirements/') || isUnder(filePath, 'spec/requirements/')
  ) && /\.(?:json|md|markdown)$/.test(filePath));
  const vitestConfig = [
    'vitest.config.ts',
    'vitest.config.mts',
    'vitest.config.js',
    'vitest.config.mjs',
  ].find((fileName) => existsSync(path.join(root, fileName))) || null;

  const requirements = requirementFiles.flatMap((filePath) => parseRequirementFile(filePath, root));
  const traceLinks = [];
  for (const filePath of [...featureFiles, ...propertyFiles, ...requirementFiles]) {
    for (const traceRef of traceRefsFromContent(readText(filePath))) {
      traceLinks.push({ traceRef, path: repoRelative(filePath, root) });
    }
  }
  for (const requirement of requirements) {
    if (!traceLinks.some((link) => link.traceRef === requirement.id && link.path === requirement.path)) {
      traceLinks.push({ traceRef: requirement.id, path: requirement.path });
    }
  }

  return {
    root,
    featureFiles: featureFiles.map((filePath) => repoRelative(filePath, root)),
    stepFiles: stepFiles.map((filePath) => repoRelative(filePath, root)),
    propertyFiles: propertyFiles.map((filePath) => repoRelative(filePath, root)),
    requirementFiles: requirementFiles.map((filePath) => repoRelative(filePath, root)),
    requirements,
    traceLinks: traceLinks.sort((a, b) => `${a.traceRef}:${a.path}`.localeCompare(`${b.traceRef}:${b.path}`)),
    vitestConfig,
  };
}

function customPropertyCommand(profile) {
  if (profile.vitestConfig) {
    return [
      'pnpm',
      'exec',
      'vitest',
      'run',
      '--config',
      path.join(profile.root, profile.vitestConfig),
      ...profile.propertyFiles.map((filePath) => path.join(profile.root, filePath)),
      '--reporter',
      'dot',
    ];
  }
  return [
    'pnpm',
    'exec',
    'vitest',
    'run',
    '--root',
    profile.root,
    ...profile.propertyFiles,
    '--reporter',
    'dot',
  ];
}

function commandText(command) {
  return command.map(shellQuote).join(' ');
}

function runCommand(command, options) {
  if (options.dryRun) {
    return { status: SKIPPED, exitCode: null, durationMs: 0, stdout: '', stderr: '', note: 'dry-run: command not executed' };
  }
  const startedAt = Date.now();
  const result = spawnSync(command[0], command.slice(1), {
    cwd: process.cwd(),
    encoding: 'utf8',
    maxBuffer: 1024 * 1024 * 20,
    env: { ...process.env, FORCE_COLOR: '0' },
  });
  const durationMs = Math.max(0, Date.now() - startedAt);
  if (result.error) {
    return { status: FAIL, exitCode: null, durationMs, stdout: result.stdout || '', stderr: result.error.message };
  }
  return {
    status: result.status === 0 ? PASS : FAIL,
    exitCode: result.status,
    durationMs,
    stdout: result.stdout || '',
    stderr: result.stderr || '',
  };
}

function buildCheck({ id, label, kind, command, traceRefs = [], artifactPaths = [], options }) {
  if (options.skippedChecks.has(id)) {
    return {
      id,
      label,
      kind,
      status: SKIPPED,
      command: commandText(command),
      exitCode: null,
      durationMs: 0,
      traceRefs,
      artifactPaths,
      message: `Skipped by --skip ${id}`,
    };
  }
  const result = runCommand(command, options);
  return {
    id,
    label,
    kind,
    status: result.status,
    command: commandText(command),
    exitCode: result.exitCode,
    durationMs: result.durationMs,
    traceRefs,
    artifactPaths,
    message: result.note || firstMeaningfulOutput(result),
  };
}

function firstMeaningfulOutput(result) {
  const combined = `${result.stderr || ''}\n${result.stdout || ''}`
    .split(/\r?\n/)
    .map((line) => line.trim())
    .filter(Boolean);
  return combined.slice(0, 5).join('\n');
}

function buildCustomSuiteCheck({ id, label, files, requiredCompanionFiles = [], command, traceRefs, options, missingMessage }) {
  if (options.skippedChecks.has(id)) {
    return { id, label, kind: 'custom-suite', status: SKIPPED, command: commandText(command), exitCode: null, durationMs: 0, traceRefs, files, message: `Skipped by --skip ${id}` };
  }
  if (files.length === 0) {
    return { id, label, kind: 'custom-suite', status: SKIPPED, command: commandText(command), exitCode: null, durationMs: 0, traceRefs, files, message: 'No custom suite files discovered.' };
  }
  if (!options.runCustomSuites) {
    return {
      id,
      label,
      kind: 'custom-suite',
      status: WARNING,
      command: commandText(command),
      exitCode: null,
      durationMs: 0,
      traceRefs,
      files,
      message: 'Custom suite discovered but not executed. Built-in property harness smoke is separate; pass --run-custom-suites to execute authored BDD/property examples.',
    };
  }
  if (requiredCompanionFiles.length === 0 && missingMessage) {
    return { id, label, kind: 'custom-suite', status: FAIL, command: commandText(command), exitCode: null, durationMs: 0, traceRefs, files, message: missingMessage };
  }
  const result = runCommand(command, options);
  return {
    id,
    label,
    kind: 'custom-suite',
    status: result.status,
    command: commandText(command),
    exitCode: result.exitCode,
    durationMs: result.durationMs,
    traceRefs,
    files,
    message: result.note || firstMeaningfulOutput(result),
  };
}

function buildActivationSummary(options = parseArgs()) {
  const generatedAt = options.generatedAt || new Date().toISOString();
  const profile = discoverProfile(options.profileRoot);
  const traceRefs = [...new Set(profile.traceLinks.map((link) => link.traceRef))].sort();
  const firstTrace = traceRefs[0] || 'spec-kit-min-smoke';
  const propertyOutput = options.propertyOutput;
  const checks = [];

  checks.push(buildCheck({
    id: 'lint',
    label: 'Lint',
    kind: 'baseline-check',
    command: ['pnpm', 'lint'],
    traceRefs: [],
    options,
  }));
  checks.push(buildCheck({
    id: 'types',
    label: 'Type check',
    kind: 'baseline-check',
    command: ['pnpm', 'types:check'],
    traceRefs: [],
    options,
  }));
  checks.push(buildCheck({
    id: 'fast',
    label: 'Fast tests',
    kind: 'baseline-check',
    command: ['pnpm', 'run', 'test:fast'],
    traceRefs: [],
    options,
  }));
  checks.push(buildCheck({
    id: 'property-smoke',
    label: 'Built-in property harness smoke',
    kind: 'built-in-harness',
    command: ['pnpm', 'run', 'test:property', '--', `--focus=${firstTrace}`, '--runs=8', `--output=${propertyOutput}`],
    traceRefs: [firstTrace],
    artifactPaths: [propertyOutput],
    options,
  }));

  checks.push(buildCustomSuiteCheck({
    id: 'bdd-custom',
    label: 'Custom BDD examples',
    files: profile.featureFiles,
    requiredCompanionFiles: profile.stepFiles,
    command: ['pnpm', 'exec', 'cucumber-js', ...profile.featureFiles.map((filePath) => path.join(profile.root, filePath)), '--import', ...profile.stepFiles.map((filePath) => path.join(profile.root, filePath))],
    traceRefs,
    options,
    missingMessage: 'BDD feature files were discovered but no step files were found under spec/bdd/steps/.',
  }));
  checks.push(buildCustomSuiteCheck({
    id: 'property-custom',
    label: 'Custom property examples',
    files: profile.propertyFiles,
    requiredCompanionFiles: profile.propertyFiles,
    command: customPropertyCommand(profile),
    traceRefs,
    options,
  }));

  const failed = checks.filter((check) => check.status === FAIL);
  const warnings = checks.filter((check) => check.status === WARNING);
  const result = failed.length > 0 ? FAIL : warnings.length > 0 ? WARNING : PASS;

  return {
    schemaVersion: 'spec-verification-kit-min-run/v1',
    generatedAt,
    result,
    profileRoot: repoRelative(profile.root),
    requirements: profile.requirements,
    discovered: {
      requirementFiles: profile.requirementFiles,
      bddFeatureFiles: profile.featureFiles,
      bddStepFiles: profile.stepFiles,
      propertyTestFiles: profile.propertyFiles,
      vitestConfig: profile.vitestConfig,
      traceLinks: profile.traceLinks,
    },
    distinctions: {
      builtInPropertyHarness: 'property-smoke runs scripts/testing/property-harness.mjs through pnpm run test:property and proves the harness path is wired.',
      customPropertySuites: 'property-custom runs authored tests/property/**/*.test.ts only when --run-custom-suites is supplied.',
      customBddSuites: 'bdd-custom runs authored spec/bdd/**/*.feature files only when --run-custom-suites is supplied and matching step files exist.',
    },
    checks,
  };
}

function renderMarkdown(summary) {
  const lines = [
    '# Spec & Verification Kit Minimum Activation Summary',
    '',
    `- Result: \`${summary.result}\``,
    `- Generated at: ${summary.generatedAt}`,
    `- Profile root: \`${summary.profileRoot}\``,
    '',
    '## Requirements / trace links',
    '',
  ];
  if (summary.requirements.length === 0 && summary.discovered.traceLinks.length === 0) {
    lines.push('- No requirement or `@trace:<id>` markers discovered.');
  } else {
    for (const requirement of summary.requirements) {
      lines.push(`- ${requirement.id}: ${requirement.title || 'Requirement'} (${requirement.path})`);
    }
    for (const link of summary.discovered.traceLinks.filter((link) => !summary.requirements.some((requirement) => requirement.id === link.traceRef && requirement.path === link.path))) {
      lines.push(`- ${link.traceRef}: ${link.path}`);
    }
  }
  lines.push('', '## Checks', '');
  for (const check of summary.checks) {
    lines.push(`- ${check.id}: \`${check.status}\` — ${check.command}`);
    if (check.traceRefs?.length) lines.push(`  - Trace refs: ${check.traceRefs.map((ref) => `\`${ref}\``).join(', ')}`);
    if (check.artifactPaths?.length) lines.push(`  - Artifacts: ${check.artifactPaths.map((artifactPath) => `\`${artifactPath}\``).join(', ')}`);
    if (check.files?.length) lines.push(`  - Files: ${check.files.map((filePath) => `\`${filePath}\``).join(', ')}`);
    if (check.message) lines.push(`  - Message: ${check.message.split(/\r?\n/)[0]}`);
  }
  lines.push('', '## Built-in versus custom suites', '');
  lines.push(`- Built-in property harness: ${summary.distinctions.builtInPropertyHarness}`);
  lines.push(`- Custom property suites: ${summary.distinctions.customPropertySuites}`);
  lines.push(`- Custom BDD suites: ${summary.distinctions.customBddSuites}`);
  return `${lines.join('\n')}\n`;
}

function writeJson(filePath, value) {
  const resolved = ensureOutputPath(filePath, 'output JSON');
  writeFileSync(resolved, `${JSON.stringify(value, null, 2)}\n`, 'utf8');
}

function writeText(filePath, value) {
  const resolved = ensureOutputPath(filePath, 'output Markdown');
  writeFileSync(resolved, value, 'utf8');
}

function run(options = parseArgs()) {
  if (options.help) {
    process.stdout.write(`${renderHelp()}\n`);
    return { status: 0, summary: null };
  }
  const summary = buildActivationSummary(options);
  const markdown = renderMarkdown(summary);
  if (!options.noWrite) {
    writeJson(options.outputJson, summary);
    writeText(options.outputMd, markdown);
  }
  process.stdout.write(`[spec-kit-min:verify] ${summary.result}: ${summary.profileRoot} -> ${options.outputJson}\n`);
  return { status: summary.result === FAIL ? 1 : 0, summary, markdown };
}

function isDirectExecution() {
  return Boolean(process.argv[1]) && import.meta.url === pathToFileURL(path.resolve(process.argv[1])).href;
}

if (isDirectExecution()) {
  try {
    const { status } = run(parseArgs(process.argv));
    process.exit(status);
  } catch (error) {
    process.stderr.write(`[spec-kit-min:verify] ${error.message}\n`);
    process.exit(1);
  }
}

export {
  buildActivationSummary,
  discoverProfile,
  parseArgs,
  renderMarkdown,
  run,
};
