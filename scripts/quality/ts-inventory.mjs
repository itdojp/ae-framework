#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';

const DEFAULT_OUTPUT = 'artifacts/metrics/ts-inventory.json';
const DEFAULT_LARGE_FILE_LINES = 400;
const TYPE_SCRIPT_EXTENSIONS = new Set(['.ts', '.tsx', '.cts', '.mts']);
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
]);

function printUsage() {
  console.log(`Usage: node scripts/quality/ts-inventory.mjs [options]

Options:
  --root <dir>                Root directory to scan (default: current working directory)
  --output <file>             Output JSON path (default: artifacts/metrics/ts-inventory.json)
  --baseline <file>           Baseline JSON path for tsIgnore comparison
  --enforce                   Exit with non-zero status when tsIgnore increased from baseline
  --large-file-lines <count>  Large-file threshold in lines (default: 400)
  --help                      Show this message
`);
}

function parsePositiveInteger(value, argName) {
  const parsed = Number.parseInt(value, 10);
  if (!Number.isFinite(parsed) || parsed <= 0) {
    throw new Error(`Invalid value for ${argName}: ${value}`);
  }
  return parsed;
}

function parseArgs(argv) {
  const options = {
    rootDir: process.cwd(),
    outputPath: DEFAULT_OUTPUT,
    baselinePath: null,
    enforce: false,
    largeFileLines: DEFAULT_LARGE_FILE_LINES,
  };

  for (let i = 0; i < argv.length; i += 1) {
    const arg = argv[i];
    if (arg === '--') {
      continue;
    }
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
    if (arg === '--baseline') {
      const next = argv[i + 1];
      if (!next) throw new Error('--baseline requires a value');
      options.baselinePath = next;
      i += 1;
      continue;
    }
    if (arg === '--large-file-lines') {
      const next = argv[i + 1];
      if (!next) throw new Error('--large-file-lines requires a value');
      options.largeFileLines = parsePositiveInteger(next, '--large-file-lines');
      i += 1;
      continue;
    }
    if (arg === '--enforce') {
      options.enforce = true;
      continue;
    }
    if (arg === '--help' || arg === '-h') {
      printUsage();
      process.exit(0);
    }
    throw new Error(`Unknown argument: ${arg}`);
  }

  return {
    rootDir: path.resolve(options.rootDir),
    outputPath: path.resolve(options.outputPath),
    baselinePath: options.baselinePath ? path.resolve(options.baselinePath) : null,
    enforce: options.enforce,
    largeFileLines: options.largeFileLines,
  };
}

function toPosixPath(value) {
  return value.split(path.sep).join('/');
}

function relativeToRoot(rootDir, absolutePath) {
  const relativePath = path.relative(rootDir, absolutePath);
  return toPosixPath(relativePath || '.');
}

function isTypeScriptFile(fileName) {
  return TYPE_SCRIPT_EXTENSIONS.has(path.extname(fileName));
}

function listTypeScriptFiles(rootDir) {
  const queue = [rootDir];
  const filePaths = [];

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
      if (entry.isFile() && isTypeScriptFile(entry.name)) {
        filePaths.push(absolutePath);
      }
    }
  }

  filePaths.sort((left, right) => left.localeCompare(right));
  return filePaths;
}

function countLines(content) {
  if (content.length === 0) {
    return 0;
  }
  return content.split(/\r?\n/u).length;
}

function countMatches(content, pattern) {
  const matches = content.match(pattern);
  return matches ? matches.length : 0;
}

function analyzeFiles(rootDir, largeFileLines) {
  const files = listTypeScriptFiles(rootDir);
  const perFile = [];

  for (const absolutePath of files) {
    const content = fs.readFileSync(absolutePath, 'utf8');
    const lines = countLines(content);
    const stats = {
      path: relativeToRoot(rootDir, absolutePath),
      lines,
      any: countMatches(content, /\bany\b/gu),
      tsIgnore: countMatches(content, /@ts-ignore\b/gu),
      tsNoCheck: countMatches(content, /@ts-nocheck\b/gu),
      eslintDisable: countMatches(content, /\beslint-disable(?:-next-line|-line)?\b/gu),
    };
    perFile.push(stats);
  }

  const totals = perFile.reduce(
    (aggregate, file) => ({
      files: aggregate.files + 1,
      lines: aggregate.lines + file.lines,
      any: aggregate.any + file.any,
      tsIgnore: aggregate.tsIgnore + file.tsIgnore,
      tsNoCheck: aggregate.tsNoCheck + file.tsNoCheck,
      eslintDisable: aggregate.eslintDisable + file.eslintDisable,
    }),
    {
      files: 0,
      lines: 0,
      any: 0,
      tsIgnore: 0,
      tsNoCheck: 0,
      eslintDisable: 0,
    },
  );

  const issueFiles = perFile
    .filter((file) => file.any > 0 || file.tsIgnore > 0 || file.tsNoCheck > 0 || file.eslintDisable > 0)
    .sort((left, right) => {
      const leftScore = left.any + left.tsIgnore + left.tsNoCheck + left.eslintDisable;
      const rightScore = right.any + right.tsIgnore + right.tsNoCheck + right.eslintDisable;
      if (leftScore !== rightScore) {
        return rightScore - leftScore;
      }
      return left.path.localeCompare(right.path);
    });

  const largeFiles = perFile
    .filter((file) => file.lines >= largeFileLines)
    .sort((left, right) => {
      if (left.lines !== right.lines) {
        return right.lines - left.lines;
      }
      return left.path.localeCompare(right.path);
    })
    .map((file) => ({ path: file.path, lines: file.lines }));

  return {
    totals,
    files: perFile,
    issueFiles,
    largeFiles,
  };
}

function readJson(filePath, description) {
  try {
    const content = fs.readFileSync(filePath, 'utf8');
    return JSON.parse(content);
  } catch (error) {
    const reason = error instanceof Error ? error.message : String(error);
    throw new Error(`Failed to read ${description}: ${filePath} (${reason})`);
  }
}

function extractTsIgnoreCountFromBaseline(baseline) {
  if (typeof baseline?.totals?.tsIgnore === 'number') {
    return baseline.totals.tsIgnore;
  }
  if (typeof baseline?.tsIgnore === 'number') {
    return baseline.tsIgnore;
  }
  throw new Error('Baseline JSON must include totals.tsIgnore or tsIgnore');
}

function buildBaselineComparison(currentTsIgnore, baselinePath, enforce) {
  if (!baselinePath) {
    return null;
  }
  const baseline = readJson(baselinePath, 'baseline');
  const baselineTsIgnore = extractTsIgnoreCountFromBaseline(baseline);
  const deltaTsIgnore = currentTsIgnore - baselineTsIgnore;
  const increased = deltaTsIgnore > 0;
  return {
    baselinePath: toPosixPath(baselinePath),
    baselineTsIgnore,
    currentTsIgnore,
    deltaTsIgnore,
    increased,
    enforce,
    shouldFail: enforce && increased,
  };
}

function writeReport(outputPath, report) {
  fs.mkdirSync(path.dirname(outputPath), { recursive: true });
  fs.writeFileSync(outputPath, `${JSON.stringify(report, null, 2)}\n`, 'utf8');
}

function main() {
  try {
    const args = parseArgs(process.argv.slice(2));
    if (!fs.existsSync(args.rootDir) || !fs.statSync(args.rootDir).isDirectory()) {
      throw new Error(`Root directory not found: ${args.rootDir}`);
    }

    const analysis = analyzeFiles(args.rootDir, args.largeFileLines);
    const baselineComparison = buildBaselineComparison(
      analysis.totals.tsIgnore,
      args.baselinePath,
      args.enforce,
    );

    const report = {
      schemaVersion: '1.0.0',
      generatedAt: new Date().toISOString(),
      rootDir: toPosixPath(args.rootDir),
      largeFileThresholdLines: args.largeFileLines,
      totals: analysis.totals,
      largeFiles: analysis.largeFiles,
      issueFiles: analysis.issueFiles,
      files: analysis.files,
      baselineComparison,
    };

    writeReport(args.outputPath, report);

    const outputDisplayPath = relativeToRoot(process.cwd(), args.outputPath);
    console.log(
      `[ts-inventory] files=${analysis.totals.files} lines=${analysis.totals.lines} any=${analysis.totals.any} tsIgnore=${analysis.totals.tsIgnore} tsNoCheck=${analysis.totals.tsNoCheck} eslintDisable=${analysis.totals.eslintDisable}`,
    );
    console.log(`[ts-inventory] large files (>=${args.largeFileLines} lines): ${analysis.largeFiles.length}`);
    console.log(`[ts-inventory] wrote report: ${outputDisplayPath}`);

    if (baselineComparison && baselineComparison.increased) {
      console.warn(
        `[ts-inventory] tsIgnore increased by +${baselineComparison.deltaTsIgnore} (baseline ${baselineComparison.baselineTsIgnore} -> current ${baselineComparison.currentTsIgnore})`,
      );
      if (baselineComparison.shouldFail) {
        console.error('[ts-inventory] enforcement enabled and tsIgnore regression detected');
        process.exit(1);
      }
    } else if (baselineComparison) {
      console.log('[ts-inventory] tsIgnore did not increase from baseline');
    }
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    console.error(`[ts-inventory] failed: ${message}`);
    process.exit(1);
  }
}

main();
