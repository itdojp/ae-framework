#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import {
  DEFAULT_COVERAGE_SUMMARY_PATH,
  buildCoverageFreshnessReport,
  getGitHead,
  relativeToRoot,
  resolveFromRoot,
  writeJsonReport,
  writeMarkdownReport,
} from '../coverage/freshness-lib.mjs';

const DEFAULT_OUTPUT = 'artifacts/testing/test-inventory.json';
const DEFAULT_MARKDOWN = 'artifacts/testing/test-inventory.md';
const TEST_FILE_PATTERN = /(?:^|\/)[^/]+(?:\.test-d\.ts|\.(?:test|spec)\.[cm]?[jt]sx?)$/iu;
const SKIP_DIRECTORIES = new Set([
  '.cache',
  '.git',
  '.hg',
  '.next',
  '.turbo',
  'artifacts',
  'coverage',
  'dist',
  'node_modules',
  'playwright-report',
  'test-results',
]);

const CATEGORY_COST_CLASS = new Map([
  ['unit', 'S'],
  ['cli-command', 'S'],
  ['agent-mcp', 'S-M'],
  ['contract', 'S-M'],
  ['workspace', 'S-M'],
  ['security', 'S-M'],
  ['formal', 'S-M'],
  ['golden', 'S-M'],
  ['provider', 'S-M'],
  ['type-contract', 'S-M'],
  ['integration', 'M'],
  ['property', 'M'],
  ['a11y', 'L'],
  ['e2e', 'L'],
  ['mbt', 'L'],
  ['performance', 'L'],
  ['mutation', 'XL'],
  ['unknown', 'M'],
]);

function printUsage() {
  console.log(`Usage: node scripts/testing/test-inventory.mjs [options]

Options:
  --root <dir>              Repository root to scan (default: current working directory)
  --output <file>           Output JSON path (default: ${DEFAULT_OUTPUT})
  --markdown <file>         Output Markdown path (default: ${DEFAULT_MARKDOWN})
  --no-markdown             Do not write Markdown output
  --coverage-summary <file> Coverage summary JSON path (default: ${DEFAULT_COVERAGE_SUMMARY_PATH})
  --head-sha <sha>          Override current git HEAD for deterministic checks
  --help                    Show this message
`);
}

function parseArgs(argv) {
  const options = {
    rootDir: process.cwd(),
    outputPath: DEFAULT_OUTPUT,
    markdownPath: DEFAULT_MARKDOWN,
    writeMarkdown: true,
    coverageSummaryPath: DEFAULT_COVERAGE_SUMMARY_PATH,
    headSha: null,
  };

  for (let i = 0; i < argv.length; i += 1) {
    const arg = argv[i];
    if (arg === '--') continue;
    if (arg === '--root') {
      const next = argv[i + 1];
      if (!next) throw new Error('--root requires a value');
      options.rootDir = next;
      i += 1;
      continue;
    }
    if (arg === '--output') {
      const next = argv[i + 1];
      if (!next) throw new Error('--output requires a value');
      options.outputPath = next;
      i += 1;
      continue;
    }
    if (arg === '--markdown') {
      const next = argv[i + 1];
      if (!next) throw new Error('--markdown requires a value');
      options.markdownPath = next;
      options.writeMarkdown = true;
      i += 1;
      continue;
    }
    if (arg === '--no-markdown') {
      options.writeMarkdown = false;
      continue;
    }
    if (arg === '--coverage-summary') {
      const next = argv[i + 1];
      if (!next) throw new Error('--coverage-summary requires a value');
      options.coverageSummaryPath = next;
      i += 1;
      continue;
    }
    if (arg === '--head-sha') {
      const next = argv[i + 1];
      if (!next) throw new Error('--head-sha requires a value');
      options.headSha = next;
      i += 1;
      continue;
    }
    if (arg === '--help' || arg === '-h') {
      printUsage();
      process.exit(0);
    }
    throw new Error(`Unknown argument: ${arg}`);
  }

  const rootDir = path.resolve(options.rootDir);
  return {
    ...options,
    rootDir,
    outputPath: resolveFromRoot(rootDir, options.outputPath),
    markdownPath: options.markdownPath ? resolveFromRoot(rootDir, options.markdownPath) : null,
  };
}

function toPosixPath(value) {
  return String(value).split(path.sep).join('/');
}

function isTestFile(relativePath) {
  return TEST_FILE_PATTERN.test(`/${relativePath}`);
}

function listTestFiles(rootDir) {
  const queue = [rootDir];
  const files = [];

  while (queue.length > 0) {
    const currentDir = queue.pop();
    if (!currentDir) continue;

    const entries = fs.readdirSync(currentDir, { withFileTypes: true });
    for (const entry of entries) {
      const absolutePath = path.join(currentDir, entry.name);
      if (entry.isDirectory()) {
        if (SKIP_DIRECTORIES.has(entry.name)) {
          continue;
        }
        queue.push(absolutePath);
        continue;
      }
      if (!entry.isFile()) {
        continue;
      }
      const relativePath = toPosixPath(path.relative(rootDir, absolutePath));
      if (isTestFile(relativePath)) {
        files.push(relativePath);
      }
    }
  }

  return files.sort((left, right) => left.localeCompare(right));
}

function categorizeTest(relativePath) {
  const p = relativePath.toLowerCase();
  if (p.startsWith('types/')) return 'type-contract';
  if (p.includes('/mutation/') || p.startsWith('tests/mutation/')) return 'mutation';
  if (p.startsWith('tests/contracts/')) return 'contract';
  if (p.startsWith('tests/property/')) return 'property';
  if (p.startsWith('tests/integration/')) return 'integration';
  if (p.startsWith('tests/a11y/')) return 'a11y';
  if (p.startsWith('tests/e2e/') || p.includes('/__e2e__/')) return 'e2e';
  if (p.startsWith('tests/mbt/')) return 'mbt';
  if (p.startsWith('tests/perf/') || p.startsWith('tests/performance/') || p.includes('/performance/')) return 'performance';
  if (p.startsWith('tests/security/') || p.startsWith('tests/unit/security-assurance/') || p.includes('/security-assurance/')) return 'security';
  if (p.startsWith('tests/formal/') || p.includes('/formalize-')) return 'formal';
  if (p.startsWith('tests/agents/') || p.startsWith('tests/codex/') || p.startsWith('tests/mcp-server/')) return 'agent-mcp';
  if (p.startsWith('tests/commands/') || p.startsWith('tests/cli/')) return 'cli-command';
  if (p.startsWith('tests/providers/')) return 'provider';
  if (p.startsWith('tests/workspace/') || p.startsWith('packages/') || p.startsWith('apps/')) return 'workspace';
  if (p.startsWith('tests/golden/') || p.includes('/golden/')) return 'golden';
  if (p.startsWith('tests/unit/')) return 'unit';
  if (p.startsWith('tests/')) return 'unit';
  return p.includes('/test') || p.includes('/spec') ? 'workspace' : 'unknown';
}

function inferUnitLikelyTarget(relativePath) {
  const unitRelativePath = relativePath.split('/').slice(2).join('/');
  if (!unitRelativePath) return 'src/*';
  const sourceRelativePath = unitRelativePath.replace(/\.(?:test|spec)(\.[cm]?[jt]sx?)$/iu, '$1');
  return `src/${sourceRelativePath}`;
}

function inferLikelyTarget(relativePath, category) {
  const p = relativePath.toLowerCase();
  if (p.startsWith('types/')) return 'types/*';
  if (p.startsWith('tests/commands/')) return 'src/commands';
  if (p.startsWith('tests/cli/')) return 'src/cli';
  if (p.startsWith('tests/agents/')) return 'src/agents';
  if (p.startsWith('tests/codex/')) return 'scripts/codex, src/mcp-server';
  if (p.startsWith('tests/mcp-server/')) return 'src/mcp-server';
  if (p.startsWith('tests/providers/')) return 'src/providers';
  if (p.startsWith('tests/contracts/')) return 'schema, fixtures, artifact producers';
  if (p.startsWith('tests/property/')) return 'property-tested source modules';
  if (p.startsWith('tests/security/') || p.includes('/security-assurance/')) return 'src/security/assurance, scripts/security';
  if (p.startsWith('tests/formal/')) return 'src/formal, packages/formalize-*';
  if (p.startsWith('tests/workspace/')) return 'packages/*, apps/*';
  if (p.startsWith('packages/')) return relativePath.split('/').slice(0, 2).join('/');
  if (p.startsWith('apps/')) return relativePath.split('/').slice(0, 2).join('/');
  if (p.startsWith('tests/a11y/')) return 'apps/web, packages/ui';
  if (p.startsWith('tests/perf/') || p.startsWith('tests/performance/')) return 'performance-sensitive source modules';
  if (p.startsWith('tests/integration/')) return 'integration boundaries';
  if (p.startsWith('tests/unit/')) return inferUnitLikelyTarget(relativePath);
  if (category === 'unit') return 'src/*';
  return 'unknown';
}

function sortRecord(record) {
  return Object.fromEntries(Object.entries(record).sort(([left], [right]) => left.localeCompare(right)));
}

function buildInventory(rootDir, options) {
  const files = listTestFiles(rootDir).map((filePath) => {
    const category = categorizeTest(filePath);
    return {
      path: filePath,
      category,
      likelyTarget: inferLikelyTarget(filePath, category),
      costClass: CATEGORY_COST_CLASS.get(category) ?? 'M',
    };
  });

  const categories = {};
  const costClasses = {};
  for (const file of files) {
    categories[file.category] = (categories[file.category] ?? 0) + 1;
    costClasses[file.costClass] = (costClasses[file.costClass] ?? 0) + 1;
  }

  const currentHead = options.headSha ?? getGitHead(rootDir);
  const coverageFreshness = buildCoverageFreshnessReport({
    rootDir,
    summaryPath: options.coverageSummaryPath,
    headSha: currentHead,
  });

  return {
    schemaVersion: 'test-inventory/v1',
    generatedAt: new Date().toISOString(),
    root: '.',
    git: {
      head: currentHead,
    },
    totals: {
      files: files.length,
      categories: sortRecord(categories),
      costClasses: sortRecord(costClasses),
    },
    files,
    coverageFreshness,
    commands: {
      inventory: 'pnpm run testing:inventory',
      coverage: 'pnpm run coverage',
      freshness: 'pnpm run coverage:freshness',
    },
  };
}

function renderMarkdown(report) {
  const categoryRows = Object.entries(report.totals.categories)
    .map(([category, count]) => `| ${category} | ${count} |`)
    .join('\n') || '| none | 0 |';
  const costRows = Object.entries(report.totals.costClasses)
    .map(([costClass, count]) => `| ${costClass} | ${count} |`)
    .join('\n') || '| none | 0 |';
  const warnings = report.coverageFreshness.warnings.length > 0
    ? report.coverageFreshness.warnings.map((warning) => `- ${warning}`).join('\n')
    : '- none';
  const sampleFiles = report.files.slice(0, 25)
    .map((file) => `| ${file.path} | ${file.category} | ${file.costClass} | ${file.likelyTarget} |`)
    .join('\n') || '| none | n/a | n/a | n/a |';

  return `# Test Inventory

Generated at: ${report.generatedAt}

## Summary

- Test files: ${report.totals.files}
- Git HEAD: ${report.git.head ?? 'unknown'}
- Coverage freshness: ${report.coverageFreshness.status}
- Report-only: ${report.coverageFreshness.reportOnly ? 'yes' : 'no'}

## Categories

| Category | Files |
| --- | ---: |
${categoryRows}

## Cost classes

| Cost class | Files |
| --- | ---: |
${costRows}

## Coverage freshness warnings

${warnings}

## Sample files

| Path | Category | Cost class | Likely target |
| --- | --- | --- | --- |
${sampleFiles}
`;
}

function main() {
  try {
    const options = parseArgs(process.argv.slice(2));
    if (!fs.existsSync(options.rootDir) || !fs.statSync(options.rootDir).isDirectory()) {
      throw new Error(`Root directory not found: ${options.rootDir}`);
    }

    const report = buildInventory(options.rootDir, options);
    writeJsonReport(options.outputPath, report);
    if (options.writeMarkdown && options.markdownPath) {
      writeMarkdownReport(options.markdownPath, renderMarkdown(report));
    }

    console.log(`[test-inventory] files=${report.totals.files} categories=${Object.keys(report.totals.categories).length} costClasses=${Object.keys(report.totals.costClasses).length}`);
    console.log(`[test-inventory] coverageFreshness=${report.coverageFreshness.status}`);
    console.log(`[test-inventory] wrote report: ${relativeToRoot(options.rootDir, options.outputPath)}`);
    if (options.writeMarkdown && options.markdownPath) {
      console.log(`[test-inventory] wrote markdown: ${relativeToRoot(options.rootDir, options.markdownPath)}`);
    }
    for (const warning of report.coverageFreshness.warnings ?? []) {
      console.warn(`[test-inventory] warning: ${warning}`);
    }
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    console.error(`[test-inventory] failed: ${message}`);
    process.exit(1);
  }
}

main();
