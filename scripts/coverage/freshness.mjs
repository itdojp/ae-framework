#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import {
  DEFAULT_COVERAGE_SUMMARY_PATH,
  DEFAULT_FRESHNESS_JSON_PATH,
  DEFAULT_FRESHNESS_MARKDOWN_PATH,
  buildCoverageFreshnessReport,
  relativeToRoot,
  renderCoverageFreshnessMarkdown,
  resolveFromRoot,
  writeJsonReport,
  writeMarkdownReport,
} from './freshness-lib.mjs';

function printUsage() {
  console.log(`Usage: node scripts/coverage/freshness.mjs [options]

Options:
  --root <dir>       Repository root to inspect (default: current working directory)
  --summary <file>   Coverage summary JSON path (default: ${DEFAULT_COVERAGE_SUMMARY_PATH})
  --output <file>    Output JSON path (default: ${DEFAULT_FRESHNESS_JSON_PATH})
  --markdown <file>  Output Markdown path (default: ${DEFAULT_FRESHNESS_MARKDOWN_PATH})
  --no-markdown      Do not write Markdown output
  --head-sha <sha>   Override current git HEAD for deterministic checks
  --help             Show this message
`);
}

function parseArgs(argv) {
  const options = {
    rootDir: process.cwd(),
    summaryPath: DEFAULT_COVERAGE_SUMMARY_PATH,
    outputPath: DEFAULT_FRESHNESS_JSON_PATH,
    markdownPath: DEFAULT_FRESHNESS_MARKDOWN_PATH,
    writeMarkdown: true,
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
    if (arg === '--summary') {
      const next = argv[i + 1];
      if (!next) throw new Error('--summary requires a value');
      options.summaryPath = next;
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
    summaryPath: options.summaryPath,
    outputPath: resolveFromRoot(rootDir, options.outputPath),
    markdownPath: options.markdownPath ? resolveFromRoot(rootDir, options.markdownPath) : null,
  };
}

function main() {
  try {
    const options = parseArgs(process.argv.slice(2));
    if (!fs.existsSync(options.rootDir) || !fs.statSync(options.rootDir).isDirectory()) {
      throw new Error(`Root directory not found: ${options.rootDir}`);
    }

    const report = buildCoverageFreshnessReport({
      rootDir: options.rootDir,
      summaryPath: options.summaryPath,
      headSha: options.headSha,
    });
    writeJsonReport(options.outputPath, report);
    if (options.writeMarkdown && options.markdownPath) {
      writeMarkdownReport(options.markdownPath, renderCoverageFreshnessMarkdown(report));
    }

    console.log(`[coverage:freshness] status=${report.status} reportOnly=${report.reportOnly}`);
    console.log(`[coverage:freshness] wrote report: ${relativeToRoot(options.rootDir, options.outputPath)}`);
    if (options.writeMarkdown && options.markdownPath) {
      console.log(`[coverage:freshness] wrote markdown: ${relativeToRoot(options.rootDir, options.markdownPath)}`);
    }
    for (const warning of report.warnings ?? []) {
      console.warn(`[coverage:freshness] warning: ${warning}`);
    }
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    console.error(`[coverage:freshness] failed: ${message}`);
    process.exit(1);
  }
}

main();
