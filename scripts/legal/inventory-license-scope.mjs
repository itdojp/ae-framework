#!/usr/bin/env node

import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { spawnSync } from 'node:child_process';

export const FIRST_PARTY_PREFIXES = [
  '.ae/',
  '.devcontainer/',
  '.github/',
  'api/',
  'apps/',
  'benchmarks/',
  'codex/',
  'config/',
  'configs/',
  'contracts/',
  'docker/',
  'docs/',
  'examples/',
  'infra/',
  'observability/',
  'packages/',
  'plans/',
  'podman/',
  'policies/',
  'policy/',
  'presets/',
  'proofs/',
  'samples/',
  'schema/',
  'scripts/',
  'security/',
  'spec/',
  'src/',
  'templates/',
  'tests/',
  'types/',
];

export const FIRST_PARTY_ROOT_FILES = [
  '.dependency-cruiser.js',
  '.dockerignore',
  '.editorconfig',
  '.env.example',
  '.gitattributes',
  '.gitignore',
  '.gitleaks.toml',
  '.npmrc',
  '.nycrc.json',
  '.tool-versions',
  'AGENTS.md',
  'CLAUDE.md',
  'CONTRIBUTING.md',
  'README.md',
  'SECURITY.md',
  'eslint.config.js',
  'package.json',
  'pnpm-lock.yaml',
  'pnpm-workspace.yaml',
  'tsconfig.json',
  'vitest.config.ts',
];

export const CONDITIONAL_PREFIXES = ['artifacts/', 'fixtures/', 'test-cassettes/'];
export const NOTICE_BASENAMES = ['LICENSE', 'NOTICE', 'COPYING'];
export const LEGAL_ROOT_FILES = ['LICENSE', 'NOTICE', 'LICENSE-SCOPE.md', 'TRADEMARKS.md', 'THIRD_PARTY_NOTICES.md'];

function normalizePath(value) {
  return value.replace(/\\/g, '/').replace(/^\.\/+/, '');
}

export function classifyTrackedPath(filePath) {
  const normalized = normalizePath(filePath);
  if (FIRST_PARTY_ROOT_FILES.includes(normalized)) {
    return 'first-party-root';
  }
  if (LEGAL_ROOT_FILES.includes(normalized)) {
    return 'legal-root';
  }
  if (FIRST_PARTY_PREFIXES.some((prefix) => normalized.startsWith(prefix))) {
    return 'first-party';
  }
  if (CONDITIONAL_PREFIXES.some((prefix) => normalized.startsWith(prefix))) {
    return 'conditional';
  }
  return 'other';
}

export function parseShortlog(shortlogText) {
  return String(shortlogText)
    .split(/\r?\n/)
    .map((line) => line.trim())
    .filter(Boolean)
    .map((line) => {
      const match = line.match(/^(\d+)\s+(.+)$/);
      if (!match) {
        return null;
      }
      return {
        commits: Number(match[1]),
        author: match[2],
      };
    })
    .filter(Boolean);
}

function runGit(rootDir, args) {
  const result = spawnSync('git', args, {
    cwd: rootDir,
    encoding: 'utf8',
  });
  if (result.status !== 0) {
    const stderr = result.stderr?.trim() || 'git command failed';
    throw new Error(stderr);
  }
  return result.stdout;
}

export function listTrackedFiles(rootDir) {
  const output = runGit(rootDir, ['ls-files', '-z']);
  return output
    .split('\0')
    .map((entry) => entry.trim())
    .filter(Boolean)
    .map(normalizePath)
    .sort((left, right) => left.localeCompare(right));
}

function readOptionalText(rootDir, relativePath) {
  const absolutePath = path.join(rootDir, relativePath);
  if (!fs.existsSync(absolutePath)) {
    return null;
  }
  return fs.readFileSync(absolutePath, 'utf8');
}

export function buildLicenseScopeAudit({
  trackedFiles,
  shortlogText,
  packageJson,
  rootLicenseText,
}) {
  const categorized = {
    firstParty: [],
    firstPartyRoot: [],
    legalRoot: [],
    conditional: [],
    other: [],
  };

  for (const filePath of trackedFiles) {
    const classification = classifyTrackedPath(filePath);
    if (classification === 'first-party') {
      categorized.firstParty.push(filePath);
    } else if (classification === 'first-party-root') {
      categorized.firstPartyRoot.push(filePath);
    } else if (classification === 'legal-root') {
      categorized.legalRoot.push(filePath);
    } else if (classification === 'conditional') {
      categorized.conditional.push(filePath);
    } else {
      categorized.other.push(filePath);
    }
  }

  const nestedNotices = trackedFiles.filter((filePath) => {
    const baseName = path.basename(filePath).toUpperCase();
    return NOTICE_BASENAMES.some((prefix) => baseName === prefix || baseName.startsWith(`${prefix}.`));
  });

  const conditionalBreakdown = Object.fromEntries(
    CONDITIONAL_PREFIXES.map((prefix) => [
      prefix.replace(/\/$/, ''),
      categorized.conditional.filter((filePath) => filePath.startsWith(prefix)).length,
    ]),
  );

  const rootLicenseSummary = rootLicenseText
    ? rootLicenseText.split(/\r?\n/).find((line) => line.trim().length > 0)?.trim() ?? null
    : null;

  return {
    schemaVersion: 'license-scope-audit/v1',
    generatedAt: new Date().toISOString(),
    repositoryLicense: rootLicenseSummary,
    packageLicenseField: packageJson?.license ?? null,
    contributorInventory: parseShortlog(shortlogText),
    trackedFilesSummary: {
      total: trackedFiles.length,
      firstParty: categorized.firstParty.length,
      firstPartyRoot: categorized.firstPartyRoot.length,
      legalRoot: categorized.legalRoot.length,
      conditional: categorized.conditional.length,
      other: categorized.other.length,
    },
    conditionalBreakdown,
    nestedNoticeFiles: nestedNotices,
    otherTrackedFiles: categorized.other,
  };
}

export function buildMarkdownReport(audit) {
  const lines = [
    '# License Migration Audit',
    '',
    `- GeneratedAt: ${audit.generatedAt}`,
    `- Repository license: ${audit.repositoryLicense ?? 'missing'}`,
    `- package.json license: ${audit.packageLicenseField ?? 'missing'}`,
    '',
    '## Tracked file summary',
    `- total: ${audit.trackedFilesSummary.total}`,
    `- first-party: ${audit.trackedFilesSummary.firstParty}`,
    `- first-party root files: ${audit.trackedFilesSummary.firstPartyRoot}`,
    `- legal root files: ${audit.trackedFilesSummary.legalRoot}`,
    `- conditional: ${audit.trackedFilesSummary.conditional}`,
    `- other: ${audit.trackedFilesSummary.other}`,
    '',
    '## Conditional breakdown',
  ];

  for (const [key, count] of Object.entries(audit.conditionalBreakdown)) {
    lines.push(`- ${key}: ${count}`);
  }

  lines.push('', '## Nested notice files');
  if (audit.nestedNoticeFiles.length === 0) {
    lines.push('- none');
  } else {
    for (const filePath of audit.nestedNoticeFiles) {
      lines.push(`- ${filePath}`);
    }
  }

  lines.push('', '## Contributor inventory');
  if (audit.contributorInventory.length === 0) {
    lines.push('- none');
  } else {
    for (const contributor of audit.contributorInventory) {
      lines.push(`- ${contributor.commits} ${contributor.author}`);
    }
  }

  if (audit.otherTrackedFiles.length > 0) {
    lines.push('', '## Other tracked files outside declared scope');
    for (const filePath of audit.otherTrackedFiles) {
      lines.push(`- ${filePath}`);
    }
  }

  return `${lines.join('\n')}\n`;
}

function parseArgs(argv) {
  const options = {
    root: process.cwd(),
    outputJson: null,
    outputMd: null,
    help: false,
  };

  for (let index = 2; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--') {
      continue;
    }
    const next = argv[index + 1];
    if (arg === '--help' || arg === '-h') {
      options.help = true;
      continue;
    }
    if (arg === '--root') {
      if (!next || next.startsWith('-')) {
        throw new Error('missing value for --root');
      }
      options.root = next;
      index += 1;
      continue;
    }
    if (arg === '--output-json') {
      if (!next || next.startsWith('-')) {
        throw new Error('missing value for --output-json');
      }
      options.outputJson = next;
      index += 1;
      continue;
    }
    if (arg === '--output-md') {
      if (!next || next.startsWith('-')) {
        throw new Error('missing value for --output-md');
      }
      options.outputMd = next;
      index += 1;
      continue;
    }
    throw new Error(`unknown option: ${arg}`);
  }

  return options;
}

function printHelp() {
  process.stdout.write(`License scope audit

Usage:
  node scripts/legal/inventory-license-scope.mjs [options]

Options:
  --root <path>         Repository root (default: current working directory)
  --output-json <path>  Write JSON report
  --output-md <path>    Write Markdown report
  --help, -h            Show this help
`);
}

export function run(argv = process.argv) {
  const options = parseArgs(argv);
  if (options.help) {
    printHelp();
    return 0;
  }

  const rootDir = path.resolve(options.root);
  const trackedFiles = listTrackedFiles(rootDir);
  const shortlogText = runGit(rootDir, ['shortlog', '-sne', '--all']);
  const packageJsonText = readOptionalText(rootDir, 'package.json');
  const packageJson = packageJsonText ? JSON.parse(packageJsonText) : null;
  const rootLicenseText = readOptionalText(rootDir, 'LICENSE');
  const audit = buildLicenseScopeAudit({
    trackedFiles,
    shortlogText,
    packageJson,
    rootLicenseText,
  });

  if (options.outputJson) {
    const outputJsonPath = path.resolve(rootDir, options.outputJson);
    fs.mkdirSync(path.dirname(outputJsonPath), { recursive: true });
    fs.writeFileSync(outputJsonPath, `${JSON.stringify(audit, null, 2)}\n`);
  }

  if (options.outputMd) {
    const outputMdPath = path.resolve(rootDir, options.outputMd);
    fs.mkdirSync(path.dirname(outputMdPath), { recursive: true });
    fs.writeFileSync(outputMdPath, buildMarkdownReport(audit));
  }

  process.stdout.write(`${JSON.stringify(audit, null, 2)}\n`);
  return 0;
}

if (import.meta.url === `file://${process.argv[1]}`) {
  try {
    process.exit(run(process.argv));
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    process.stderr.write(`[license-scope-audit] ${message}\n`);
    process.exit(1);
  }
}
