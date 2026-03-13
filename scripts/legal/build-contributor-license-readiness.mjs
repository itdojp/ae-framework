#!/usr/bin/env node

import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { pathToFileURL } from 'node:url';
import { resolveGeneratedAt, resolveGitHeadSha } from './inventory-license-scope.mjs';

function readJsonFile(filePath) {
  return JSON.parse(fs.readFileSync(filePath, 'utf8'));
}

function classifyContributor(author) {
  const value = String(author || '');
  const lower = value.toLowerCase();
  if (/\bbot\b/.test(lower) || /\bclaude code\b/.test(lower) || /(^|[^a-z])agent([^a-z]|$)/.test(lower)) {
    return 'bot-like';
  }
  if (value.trim().length === 0) {
    return 'unknown';
  }
  return 'human-like';
}

function usesNoreply(author) {
  return /@users\.noreply\.github\.com(?:>|$)/i.test(String(author || ''));
}

export function buildContributorLicenseReadinessAudit({
  scopeAudit,
  scopeAuditPath,
  gitHeadSha,
  generatedAt = new Date().toISOString(),
}) {
  const contributorInventory = Array.isArray(scopeAudit.contributorInventory)
    ? scopeAudit.contributorInventory
    : [];

  const contributors = contributorInventory
    .map((entry) => ({
      author: String(entry?.author || '').trim(),
      commits: Number.isInteger(entry?.commits) ? entry.commits : 0,
    }))
    .filter((entry) => entry.author.length > 0)
    .map((entry) => ({
      ...entry,
      kind: classifyContributor(entry.author),
      usesNoreply: usesNoreply(entry.author),
    }));

  return {
    schemaVersion: 'contributor-license-readiness-audit/v1',
    generatedAt,
    gitHeadSha:
      typeof scopeAudit?.gitHeadSha === 'string' && scopeAudit.gitHeadSha.length > 0
        ? (() => {
            if (gitHeadSha && scopeAudit.gitHeadSha !== gitHeadSha) {
              throw new Error('scope audit gitHeadSha does not match the current repository HEAD');
            }
            return scopeAudit.gitHeadSha;
          })()
        : (gitHeadSha ?? null),
    inputs: {
      scopeAuditPath,
      repositoryLicense: scopeAudit.repositoryLicense ?? null,
      packageLicenseField: scopeAudit.packageLicenseField ?? null,
      contributorCount: contributors.length,
    },
    summary: {
      humanLikeCount: contributors.filter((entry) => entry.kind === 'human-like').length,
      botLikeCount: contributors.filter((entry) => entry.kind === 'bot-like').length,
      noreplyCount: contributors.filter((entry) => entry.usesNoreply).length,
      topContributorCommits: contributors.length === 0 ? 0 : Math.max(...contributors.map((entry) => entry.commits)),
    },
    contributors,
    readiness: {
      status: 'repo-facts-ready',
      recommendedAction: 'human-legal-review',
      legalDecisionRequired: true,
      notes: [
        'Repo facts do not establish relicensing authority.',
        'Noreply or bot identities may require manual normalization before legal review.',
      ],
    },
  };
}

const escapeTableCell = (value) =>
  String(value ?? '')
    .replace(/\\/g, '\\\\')
    .replace(/`/g, '\\`')
    .replace(/\|/g, '\\|')
    .replace(/\r?\n/g, '<br>');

const codeCell = (value) => `\`${escapeTableCell(value)}\``;

export function renderMarkdownReport(audit) {
  const lines = [
    '# Contributor License Readiness Audit',
    '',
    `- generatedAt: ${audit.generatedAt}`,
    `- gitHeadSha: ${audit.gitHeadSha ?? 'missing'}`,
    `- repository license: ${audit.inputs.repositoryLicense ?? 'missing'}`,
    `- package.json license: ${audit.inputs.packageLicenseField ?? 'missing'}`,
    `- contributor count: ${audit.inputs.contributorCount}`,
    '',
    '## Summary',
    `- human-like: ${audit.summary.humanLikeCount}`,
    `- bot-like: ${audit.summary.botLikeCount}`,
    `- noreply: ${audit.summary.noreplyCount}`,
    `- top contributor commits: ${audit.summary.topContributorCommits}`,
    '',
    '## Contributors',
    '',
    '| Author | Commits | Kind | Noreply |',
    '| --- | ---: | --- | --- |',
  ];

  for (const contributor of audit.contributors) {
    lines.push(
      `| ${codeCell(contributor.author)} | ${contributor.commits} | ${contributor.kind} | ${contributor.usesNoreply ? 'yes' : 'no'} |`,
    );
  }

  lines.push('', '## Readiness notes');
  for (const note of audit.readiness.notes) {
    lines.push(`- ${note}`);
  }

  return `${lines.join('\n')}\n`;
}

function parseArgs(argv) {
  const options = {
    root: process.cwd(),
    scopeAudit: 'artifacts/reference/legal/license-scope-audit.json',
    outputJson: null,
    outputMd: null,
    help: false,
  };

  for (let index = 2; index < argv.length; index += 1) {
    const arg = argv[index];
    const next = argv[index + 1];
    if (arg === '--') continue;
    if (arg === '--help' || arg === '-h') {
      options.help = true;
      continue;
    }
    if (arg === '--root') {
      if (!next || next.startsWith('-')) throw new Error('missing value for --root');
      options.root = next;
      index += 1;
      continue;
    }
    if (arg === '--scope-audit') {
      if (!next || next.startsWith('-')) throw new Error('missing value for --scope-audit');
      options.scopeAudit = next;
      index += 1;
      continue;
    }
    if (arg === '--output-json') {
      if (!next || next.startsWith('-')) throw new Error('missing value for --output-json');
      options.outputJson = next;
      index += 1;
      continue;
    }
    if (arg === '--output-md') {
      if (!next || next.startsWith('-')) throw new Error('missing value for --output-md');
      options.outputMd = next;
      index += 1;
      continue;
    }
    throw new Error(`unknown option: ${arg}`);
  }
  return options;
}

function printHelp() {
  process.stdout.write(`Contributor license readiness audit

Usage:
  node scripts/legal/build-contributor-license-readiness.mjs [options]

Options:
  --root <path>         Repository root (default: current working directory)
  --scope-audit <path>  Input JSON from license scope audit
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
  const scopeAuditPath = path.resolve(rootDir, options.scopeAudit);
  const audit = buildContributorLicenseReadinessAudit({
    scopeAudit: readJsonFile(scopeAuditPath),
    scopeAuditPath: path.relative(rootDir, scopeAuditPath).replace(/\\/g, '/'),
    gitHeadSha: resolveGitHeadSha(rootDir),
    generatedAt: resolveGeneratedAt(),
  });

  if (options.outputJson) {
    const outputPath = path.resolve(rootDir, options.outputJson);
    fs.mkdirSync(path.dirname(outputPath), { recursive: true });
    fs.writeFileSync(outputPath, `${JSON.stringify(audit, null, 2)}\n`);
  }
  if (options.outputMd) {
    const outputPath = path.resolve(rootDir, options.outputMd);
    fs.mkdirSync(path.dirname(outputPath), { recursive: true });
    fs.writeFileSync(outputPath, renderMarkdownReport(audit));
  }
  if (!options.outputJson && !options.outputMd) {
    process.stdout.write(`${JSON.stringify(audit, null, 2)}\n`);
  }
  return 0;
}

const isExecutedAsMain = (() => {
  const entry = process.argv[1];
  if (!entry) return false;
  return pathToFileURL(path.resolve(entry)).href === import.meta.url;
})();

if (isExecutedAsMain) {
  try {
    process.exitCode = run();
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    process.stderr.write(`${message}\n`);
    process.exitCode = 1;
  }
}
