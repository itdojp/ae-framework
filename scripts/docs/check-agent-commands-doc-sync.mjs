#!/usr/bin/env node

import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const DEFAULT_WORKFLOW_PATH = '.github/workflows/agent-commands.yml';
const DEFAULT_OUTPUT_PATH = 'docs/agents/commands.md';
const __filename = fileURLToPath(import.meta.url);

function toSortedUnique(values) {
  return [...new Set(values)].sort((a, b) => a.localeCompare(b));
}

function splitWorkflowSections(workflowText) {
  const source = String(workflowText || '');
  const marker = '\n  handle_issue:\n';
  const index = source.indexOf(marker);
  if (index < 0) {
    return {
      prSection: source,
      issueSection: '',
    };
  }
  return {
    prSection: source.slice(0, index),
    issueSection: source.slice(index),
  };
}

function extractPrCommands(prSection) {
  const commands = [];
  const pattern = /case\s+'([^']+)':/g;
  for (const match of prSection.matchAll(pattern)) {
    const command = String(match[1] || '').trim();
    if (!command.startsWith('/')) continue;
    commands.push(command);
  }
  return toSortedUnique(commands);
}

function extractIssueCommands(issueSection) {
  const commands = [];
  const pattern = /body\.startsWith\('([^']+)'\)/g;
  for (const match of issueSection.matchAll(pattern)) {
    const command = String(match[1] || '').trim();
    if (!command.startsWith('/')) continue;
    commands.push(command);
  }
  return toSortedUnique(commands);
}

function extractQuotedLabels(fragment) {
  const labels = [];
  const pattern = /['"]([^'"]+)['"]/g;
  for (const match of fragment.matchAll(pattern)) {
    const value = String(match[1] || '').trim();
    if (!value) continue;
    labels.push(value);
  }
  return labels;
}

function extractLabelMetadata(workflowText) {
  const { prSection, issueSection } = splitWorkflowSections(workflowText);
  const prLabels = [];
  const issueLabels = [];
  const dynamicLabels = [];

  for (const match of prSection.matchAll(/addLabels\(\[([^\]]*)\]\)/g)) {
    prLabels.push(...extractQuotedLabels(match[1] || ''));
  }
  for (const match of issueSection.matchAll(/add\(\[([^\]]*)\]\)/g)) {
    issueLabels.push(...extractQuotedLabels(match[1] || ''));
  }

  if (prSection.includes('coverage:${n}')) {
    dynamicLabels.push('coverage:<0-100>');
  }
  if (prSection.includes('perf:${n}')) {
    dynamicLabels.push('perf:<0-100>');
  }
  if (prSection.includes('lh:${n}')) {
    dynamicLabels.push('lh:<0-100>');
  }
  if (prSection.includes('handoff:agent-${m.toLowerCase()}')) {
    dynamicLabels.push('handoff:agent-{a|b|c}');
  }

  return {
    prLabels: toSortedUnique(prLabels),
    issueLabels: toSortedUnique(issueLabels),
    dynamicLabels: toSortedUnique(dynamicLabels),
  };
}

function renderMarkdown({ prCommands, issueCommands, prLabels, issueLabels, dynamicLabels }) {
  const lines = [
    '# Agent Commands Catalog',
    '',
    '> この文書は `.github/workflows/agent-commands.yml` から自動生成されます。手動編集しないでください。',
    '',
    '## PR向け Slash Commands',
    '',
  ];

  if (prCommands.length === 0) {
    lines.push('- (none)');
  } else {
    for (const command of prCommands) {
      lines.push(`- \`${command}\``);
    }
  }

  lines.push('', '## Issue向け Slash Commands', '');

  if (issueCommands.length === 0) {
    lines.push('- (none)');
  } else {
    for (const command of issueCommands) {
      lines.push(`- \`${command}\``);
    }
  }

  lines.push('', '## PRコマンドで付与される静的ラベル', '');

  if (prLabels.length === 0) {
    lines.push('- (none)');
  } else {
    for (const label of prLabels) {
      lines.push(`- \`${label}\``);
    }
  }

  lines.push('', '## Issueコマンドで付与される静的ラベル', '');

  if (issueLabels.length === 0) {
    lines.push('- (none)');
  } else {
    for (const label of issueLabels) {
      lines.push(`- \`${label}\``);
    }
  }

  lines.push('', '## 動的ラベルパターン', '');

  if (dynamicLabels.length === 0) {
    lines.push('- (none)');
  } else {
    for (const pattern of dynamicLabels) {
      lines.push(`- \`${pattern}\``);
    }
  }

  lines.push('', '## Source', '', '- `.github/workflows/agent-commands.yml`', '');
  return `${lines.join('\n')}`;
}

function parseArgs(argv) {
  const options = {
    rootDir: process.cwd(),
    workflowPath: DEFAULT_WORKFLOW_PATH,
    outputPath: DEFAULT_OUTPUT_PATH,
    write: false,
  };
  for (let index = 2; index < argv.length; index += 1) {
    const value = argv[index];
    if (value.startsWith('--root=')) {
      options.rootDir = path.resolve(value.slice('--root='.length));
      continue;
    }
    if (value === '--root' && argv[index + 1] && !argv[index + 1].startsWith('-')) {
      options.rootDir = path.resolve(argv[++index]);
      continue;
    }
    if (value === '--write') {
      options.write = true;
      continue;
    }
    if ((value === '--workflow' || value === '--workflow-path') && argv[index + 1]) {
      options.workflowPath = argv[++index];
      continue;
    }
    if (value.startsWith('--workflow=')) {
      options.workflowPath = value.slice('--workflow='.length);
      continue;
    }
    if ((value === '--output' || value === '--output-path') && argv[index + 1]) {
      options.outputPath = argv[++index];
      continue;
    }
    if (value.startsWith('--output=')) {
      options.outputPath = value.slice('--output='.length);
      continue;
    }
  }
  return options;
}

function ensureDirectory(filePath) {
  fs.mkdirSync(path.dirname(filePath), { recursive: true });
}

function buildCatalogFromWorkflow(workflowText) {
  const { prSection, issueSection } = splitWorkflowSections(workflowText);
  const prCommands = extractPrCommands(prSection);
  const issueCommands = extractIssueCommands(issueSection);
  const labels = extractLabelMetadata(workflowText);
  return renderMarkdown({
    prCommands,
    issueCommands,
    prLabels: labels.prLabels,
    issueLabels: labels.issueLabels,
    dynamicLabels: labels.dynamicLabels,
  });
}

export function main(argv = process.argv) {
  const options = parseArgs(argv);
  const workflowPath = path.resolve(options.rootDir, options.workflowPath);
  const outputPath = path.resolve(options.rootDir, options.outputPath);

  const workflowText = fs.readFileSync(workflowPath, 'utf8');
  const expected = buildCatalogFromWorkflow(workflowText);

  if (options.write) {
    ensureDirectory(outputPath);
    fs.writeFileSync(outputPath, expected);
    process.stdout.write(`Updated ${options.outputPath}\n`);
    return 0;
  }

  if (!fs.existsSync(outputPath)) {
    process.stderr.write(`Missing generated file: ${options.outputPath}\n`);
    process.stderr.write('Run: node scripts/docs/check-agent-commands-doc-sync.mjs --write\n');
    return 1;
  }

  const current = fs.readFileSync(outputPath, 'utf8');
  if (current !== expected) {
    process.stderr.write(`Out of sync: ${options.outputPath}\n`);
    process.stderr.write('Run: node scripts/docs/check-agent-commands-doc-sync.mjs --write\n');
    return 1;
  }

  process.stdout.write('Agent commands docs are in sync.\n');
  return 0;
}

if (process.argv[1] && path.resolve(process.argv[1]) === __filename) {
  process.exit(main(process.argv));
}

export {
  buildCatalogFromWorkflow,
  extractIssueCommands,
  extractLabelMetadata,
  extractPrCommands,
  parseArgs,
  renderMarkdown,
  splitWorkflowSections,
};
