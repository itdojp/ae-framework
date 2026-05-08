import fs from 'node:fs';
import path from 'node:path';
import { execFileSync } from 'node:child_process';

export const DEFAULT_COVERAGE_SUMMARY_PATH = 'coverage/coverage-summary.json';
export const DEFAULT_FRESHNESS_JSON_PATH = 'artifacts/testing/coverage-freshness.json';
export const DEFAULT_FRESHNESS_MARKDOWN_PATH = 'artifacts/testing/coverage-freshness.md';

const METRIC_NAMES = ['lines', 'statements', 'functions', 'branches'];
const MIN_SHA_PREFIX_LENGTH = 7;
const MAX_SHA_LENGTH = 64;
const HEX_SHA_PATTERN = /^[0-9a-f]+$/iu;

export function toPosixPath(value) {
  return String(value).split(path.sep).join('/');
}

export function relativeToRoot(rootDir, absolutePath) {
  const relativePath = path.relative(rootDir, absolutePath);
  return toPosixPath(relativePath || '.');
}

export function resolveFromRoot(rootDir, maybeRelativePath) {
  return path.isAbsolute(maybeRelativePath)
    ? path.resolve(maybeRelativePath)
    : path.resolve(rootDir, maybeRelativePath);
}

function firstString(...values) {
  for (const value of values) {
    if (typeof value === 'string' && value.trim().length > 0) {
      return value.trim();
    }
  }
  return null;
}

function firstNumber(...values) {
  for (const value of values) {
    if (typeof value === 'number' && Number.isFinite(value)) {
      return value;
    }
  }
  return null;
}

function normalizeSha(value) {
  if (typeof value !== 'string') return null;
  const normalized = value.trim().toLowerCase();
  if (!normalized) return null;
  return normalized;
}

function isComparableSha(value) {
  return (
    typeof value === 'string'
    && value.length >= MIN_SHA_PREFIX_LENGTH
    && value.length <= MAX_SHA_LENGTH
    && HEX_SHA_PATTERN.test(value)
  );
}

function shasMatch(left, right) {
  const leftSha = normalizeSha(left);
  const rightSha = normalizeSha(right);
  if (!isComparableSha(leftSha) || !isComparableSha(rightSha)) return false;
  return leftSha === rightSha || leftSha.startsWith(rightSha) || rightSha.startsWith(leftSha);
}

function extractGitSha(summary) {
  return firstString(
    summary?.metadata?.git?.head,
    summary?.metadata?.git?.sha,
    summary?.metadata?.gitHead,
    summary?.metadata?.gitSha,
    summary?.metadata?.headSha,
    summary?.git?.head,
    summary?.git?.sha,
    summary?.git?.commit,
    summary?.gitHead,
    summary?.gitSha,
    summary?.headSha,
    summary?.commit,
    summary?.commitSha,
  );
}

function extractTimestamp(summary) {
  return firstString(
    summary?.metadata?.timestamp,
    summary?.metadata?.generatedAt,
    summary?.metadata?.createdAt,
    summary?.generatedAt,
    summary?.createdAt,
    summary?.timestamp,
    summary?.git?.timestamp,
  );
}

function extractSourcePath(summary) {
  return firstString(
    summary?.metadata?.sourcePath,
    summary?.metadata?.coverageSummaryPath,
    summary?.coverageSummaryPath,
    summary?.sourcePath,
    summary?.path,
  );
}


function normalizeReportSourcePath(rootDir, sourcePath, fallbackPath) {
  if (!sourcePath) return fallbackPath;
  if (path.isAbsolute(sourcePath)) {
    const relativePath = path.relative(rootDir, path.resolve(sourcePath));
    if (relativePath && !relativePath.startsWith('..') && !path.isAbsolute(relativePath)) {
      return toPosixPath(relativePath);
    }
  }
  return toPosixPath(sourcePath);
}

function extractMetric(summary, name) {
  const metric = summary?.total?.[name];
  if (!metric || typeof metric !== 'object') {
    return null;
  }
  return {
    pct: firstNumber(metric.pct),
    covered: firstNumber(metric.covered),
    total: firstNumber(metric.total),
    skipped: firstNumber(metric.skipped),
  };
}

function extractMetrics(summary) {
  const metrics = {};
  for (const name of METRIC_NAMES) {
    const metric = extractMetric(summary, name);
    if (metric) {
      metrics[name] = metric;
    }
  }
  return metrics;
}

export function getGitHead(rootDir) {
  try {
    return execFileSync('git', ['-C', rootDir, 'rev-parse', 'HEAD'], {
      encoding: 'utf8',
      stdio: ['ignore', 'pipe', 'ignore'],
    }).trim();
  } catch {
    return null;
  }
}

function readCoverageSummary(summaryPath) {
  if (!fs.existsSync(summaryPath)) {
    return { exists: false, summary: null, parseError: null, stat: null };
  }

  const stat = fs.statSync(summaryPath);
  try {
    return {
      exists: true,
      summary: JSON.parse(fs.readFileSync(summaryPath, 'utf8')),
      parseError: null,
      stat,
    };
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    return { exists: true, summary: null, parseError: message, stat };
  }
}

export function buildCoverageFreshnessReport(options = {}) {
  const rootDir = path.resolve(options.rootDir ?? process.cwd());
  const summaryPath = resolveFromRoot(rootDir, options.summaryPath ?? DEFAULT_COVERAGE_SUMMARY_PATH);
  const currentHead = options.headSha ?? getGitHead(rootDir);
  const checkedAt = options.generatedAt ?? new Date().toISOString();
  const coverage = readCoverageSummary(summaryPath);
  const summaryRelativePath = relativeToRoot(rootDir, summaryPath);
  const updateCommand = options.updateCommand ?? 'pnpm run coverage';

  const baseReport = {
    schemaVersion: 'coverage-freshness/v1',
    checkedAt,
    root: '.',
    summaryPath: summaryRelativePath,
    currentHead,
    summaryGitSha: null,
    timestamp: null,
    timestampSource: null,
    sourcePath: summaryRelativePath,
    sourcePathSource: 'default-summary-path',
    status: 'missing',
    isFresh: false,
    reportOnly: true,
    updateCommand,
    metrics: {},
    warnings: [],
  };

  if (!coverage.exists) {
    return {
      ...baseReport,
      warnings: [
        `coverage summary is missing at ${summaryRelativePath}; run ${updateCommand} to refresh coverage evidence`,
      ],
    };
  }

  const mtimeIso = coverage.stat ? coverage.stat.mtime.toISOString() : null;
  if (coverage.parseError || !coverage.summary) {
    return {
      ...baseReport,
      timestamp: mtimeIso,
      timestampSource: mtimeIso ? 'file-mtime' : null,
      status: 'invalid',
      warnings: [
        `coverage summary is invalid JSON at ${summaryRelativePath}: ${coverage.parseError}`,
        `run ${updateCommand} to regenerate coverage evidence`,
      ],
    };
  }

  const summary = coverage.summary;
  const summaryGitSha = extractGitSha(summary);
  const explicitTimestamp = extractTimestamp(summary);
  const sourcePath = extractSourcePath(summary);
  const timestamp = explicitTimestamp ?? mtimeIso;
  const timestampSource = explicitTimestamp ? 'summary-metadata' : (mtimeIso ? 'file-mtime' : null);
  const sourcePathValue = normalizeReportSourcePath(rootDir, sourcePath, summaryRelativePath);
  const sourcePathSource = sourcePath ? 'summary-metadata' : 'default-summary-path';
  const metrics = extractMetrics(summary);
  const warnings = [];
  let status = 'unknown';
  let isFresh = false;

  if (summaryGitSha && currentHead && shasMatch(summaryGitSha, currentHead)) {
    status = 'fresh';
    isFresh = true;
  } else if (summaryGitSha && currentHead) {
    status = 'stale';
    warnings.push(
      `coverage summary git SHA ${summaryGitSha} does not match current HEAD ${currentHead}; run ${updateCommand}`,
    );
  } else if (!summaryGitSha) {
    status = 'unknown';
    warnings.push(
      `coverage summary does not include git SHA metadata; freshness cannot be proven. Run ${updateCommand} and attach commit metadata if this artifact is used for review evidence`,
    );
  } else {
    status = 'unknown';
    warnings.push(
      `current git HEAD could not be determined; freshness cannot be proven for coverage summary SHA ${summaryGitSha}`,
    );
  }

  return {
    ...baseReport,
    summaryGitSha,
    timestamp,
    timestampSource,
    sourcePath: sourcePathValue,
    sourcePathSource,
    status,
    isFresh,
    metrics,
    warnings,
  };
}

function formatMetric(metric) {
  if (!metric) return 'n/a';
  const pct = typeof metric.pct === 'number' ? `${metric.pct}%` : 'n/a';
  const covered = typeof metric.covered === 'number' ? metric.covered : 'n/a';
  const total = typeof metric.total === 'number' ? metric.total : 'n/a';
  return `${pct} (${covered}/${total})`;
}

export function renderCoverageFreshnessMarkdown(report) {
  const lines = [
    '# Coverage Freshness',
    '',
    '| Field | Value |',
    '| --- | --- |',
    `| Status | ${report.status} |`,
    `| Report-only | ${report.reportOnly ? 'yes' : 'no'} |`,
    `| Current HEAD | ${report.currentHead ?? 'unknown'} |`,
    `| Coverage SHA | ${report.summaryGitSha ?? 'unknown'} |`,
    `| Coverage timestamp | ${report.timestamp ?? 'unknown'} |`,
    `| Timestamp source | ${report.timestampSource ?? 'unknown'} |`,
    `| Summary path | ${report.summaryPath} |`,
    `| Source path | ${report.sourcePath ?? 'unknown'} |`,
    `| Update command | \`${report.updateCommand}\` |`,
    '',
    '## Metrics',
    '',
    '| Metric | Value |',
    '| --- | ---: |',
  ];

  for (const name of METRIC_NAMES) {
    lines.push(`| ${name} | ${formatMetric(report.metrics?.[name])} |`);
  }

  lines.push('', '## Warnings', '');
  if (Array.isArray(report.warnings) && report.warnings.length > 0) {
    for (const warning of report.warnings) {
      lines.push(`- ${warning}`);
    }
  } else {
    lines.push('- none');
  }

  return `${lines.join('\n')}\n`;
}

export function writeJsonReport(outputPath, report) {
  fs.mkdirSync(path.dirname(outputPath), { recursive: true });
  fs.writeFileSync(outputPath, `${JSON.stringify(report, null, 2)}\n`, 'utf8');
}

export function writeMarkdownReport(outputPath, markdown) {
  fs.mkdirSync(path.dirname(outputPath), { recursive: true });
  fs.writeFileSync(outputPath, markdown, 'utf8');
}
