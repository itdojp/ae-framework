import { existsSync, readFileSync, statSync } from 'node:fs';
import path from 'node:path';
import { glob } from 'glob';
import chalk from 'chalk';
import { toMessage } from '../utils/error-utils.js';
import type {
  ConformanceRuleCategory,
  ConformanceVerificationResult,
  VerificationStatus,
  ViolationDetails,
  ViolationSeverity,
} from '../conformance/types.js';

const REPORT_SCHEMA_VERSION = '1.0.0';
const VIOLATION_SEVERITIES = ['critical', 'major', 'minor', 'info', 'warning'] as ViolationSeverity[];
const CONFORMANCE_CATEGORIES = [
  'data_validation',
  'api_contract',
  'business_logic',
  'security_policy',
  'performance_constraint',
  'resource_usage',
  'state_invariant',
  'behavioral_constraint',
  'integration_requirement',
  'compliance_rule',
] as ConformanceRuleCategory[];

export type ConformanceReportStatus = 'success' | 'failure' | 'skipped';

export interface AggregatedRunInput {
  file: string;
  absolutePath: string;
  result: ConformanceVerificationResult;
  timestamp: string;
}

export interface ConformanceReportSummary {
  schemaVersion: string;
  generatedAt: string;
  status: ConformanceReportStatus;
  runsAnalyzed: number;
  statusBreakdown: Record<VerificationStatus, number>;
  totals: {
    rulesExecuted: number;
    rulesPassed: number;
    rulesFailed: number;
    rulesErrored: number;
    rulesSkipped: number;
    totalViolations: number;
    uniqueRules: number;
    uniqueViolationRules: number;
  };
  severityTotals: Record<ViolationSeverity, number>;
  categoryTotals: Record<ConformanceRuleCategory, number>;
  severityTrends: Array<{
    severity: ViolationSeverity;
    current: number;
    previous: number;
    trend: 'increasing' | 'decreasing' | 'stable';
  }>;
  topViolations: Array<{
    ruleId: string;
    ruleName: string;
    count: number;
    lastObserved: string | null;
  }>;
  latestRun?: {
    file: string;
    timestamp: string;
    status: VerificationStatus;
    environment: string;
    version: string;
    rulesExecuted: number;
    rulesFailed: number;
    totalViolations: number;
  };
  inputs: Array<{
    file: string;
    timestamp: string;
    status: VerificationStatus;
    environment: string;
    version: string;
    totalViolations: number;
  }>;
  notes?: string;
}

export interface ConformanceResultDiscoveryOptions {
  inputs: string[];
  globs: string[];
  directory?: string;
  pattern?: string;
  useDefaults: boolean;
}

export async function resolveConformanceResultFiles(
  options: ConformanceResultDiscoveryOptions,
): Promise<string[]> {
  const resolved = new Set<string>();
  const missingExplicit: string[] = [];
  const patterns: string[] = [];

  for (const inputPath of options.inputs) {
    if (looksLikeGlob(inputPath)) {
      patterns.push(path.resolve(inputPath));
      continue;
    }

    const absolute = path.resolve(inputPath);
    if (existsSync(absolute)) {
      resolved.add(absolute);
    } else {
      missingExplicit.push(inputPath);
    }
  }

  for (const globPattern of options.globs) {
    if (globPattern.length > 0) {
      patterns.push(path.resolve(globPattern));
    }
  }

  if (options.directory) {
    const baseDir = path.resolve(options.directory);
    const derivedPattern = options.pattern ?? '*.json';
    patterns.push(path.join(baseDir, derivedPattern));
  }

  if (options.useDefaults) {
    const defaultCandidates = [
      'conformance-results.json',
      path.join('artifacts/hermetic-reports', 'conformance', '*.json'),
      path.join('reports', 'conformance', '*.json'),
    ];

    for (const candidate of defaultCandidates) {
      if (looksLikeGlob(candidate)) {
        patterns.push(path.resolve(candidate));
      } else {
        const absolute = path.resolve(candidate);
        if (existsSync(absolute)) {
          resolved.add(absolute);
        }
      }
    }
  }

  for (const patternPath of patterns) {
    const matches = await glob(patternPath, { nodir: true, absolute: true });
    for (const match of matches) {
      if (existsSync(match)) {
        resolved.add(path.resolve(match));
      }
    }
  }

  if (missingExplicit.length > 0) {
    for (const missing of missingExplicit) {
      console.warn(chalk.yellow(`⚠️  Conformance result not found: ${missing}`));
    }
  }

  return Array.from(resolved).sort();
}

export function loadConformanceResults(files: string[]): { runs: AggregatedRunInput[]; failedFiles: string[] } {
  const runs: AggregatedRunInput[] = [];
  const failedFiles: string[] = [];

  for (const absolutePath of files) {
    try {
      const raw = readFileSync(absolutePath, 'utf-8');
      const parsed = JSON.parse(raw) as ConformanceVerificationResult;
      if (!parsed || typeof parsed !== 'object' || !parsed.summary) {
        console.warn(chalk.yellow(`⚠️  Skipping ${toRelativePath(absolutePath)}: missing conformance summary.`));
        continue;
      }

      const timestamp = resolveResultTimestamp(parsed, absolutePath);
      runs.push({
        file: toRelativePath(absolutePath),
        absolutePath,
        result: parsed,
        timestamp,
      });
    } catch (error: unknown) {
      console.error(chalk.red(`❌ Failed to read result ${toRelativePath(absolutePath)}: ${toMessage(error)}`));
      failedFiles.push(toRelativePath(absolutePath));
    }
  }

  return { runs, failedFiles };
}

export function buildConformanceReportSummary(
  runs: AggregatedRunInput[],
  failedFiles: string[],
): ConformanceReportSummary {
  const generatedAt = new Date().toISOString();
  const statusBreakdown: Record<VerificationStatus, number> = {
    pass: 0,
    fail: 0,
    skip: 0,
    error: 0,
    timeout: 0,
  };

  if (runs.length === 0) {
    const summary: ConformanceReportSummary = {
      schemaVersion: REPORT_SCHEMA_VERSION,
      generatedAt,
      status: failedFiles.length > 0 ? 'failure' : 'skipped',
      runsAnalyzed: 0,
      statusBreakdown,
      totals: {
        rulesExecuted: 0,
        rulesPassed: 0,
        rulesFailed: 0,
        rulesErrored: 0,
        rulesSkipped: 0,
        totalViolations: 0,
        uniqueRules: 0,
        uniqueViolationRules: 0,
      },
      severityTotals: createEmptySeverityMap(),
      categoryTotals: createEmptyCategoryMap(),
      severityTrends: VIOLATION_SEVERITIES.map((severity) => ({
        severity,
        current: 0,
        previous: 0,
        trend: 'stable' as const,
      })),
      topViolations: [],
      inputs: [],
      notes:
        failedFiles.length > 0
          ? `Failed to load ${failedFiles.length} conformance result file(s).`
          : 'No conformance results were discovered.',
    };

    if (failedFiles.length > 0) {
      const now = new Date().toISOString();
      failedFiles.forEach((file) => {
        statusBreakdown.error += 1;
        summary.inputs.push({
          file,
          timestamp: now,
          status: 'error',
          environment: 'unknown',
          version: 'unknown',
          totalViolations: 0,
        });
      });
    }

    return summary;
  }

  const totals = {
    rulesExecuted: 0,
    rulesPassed: 0,
    rulesFailed: 0,
    rulesErrored: 0,
    rulesSkipped: 0,
    totalViolations: 0,
    uniqueRules: 0,
    uniqueViolationRules: 0,
  };

  const severityTotals = createEmptySeverityMap();
  const categoryTotals = createEmptyCategoryMap();
  const uniqueRules = new Set<string>();
  const uniqueViolationRules = new Set<string>();
  const violationAccumulator = new Map<string, { ruleId: string; ruleName: string; count: number; lastObserved: string | null }>();

  const sortedRuns = [...runs].sort((a, b) => parseTimestamp(a.timestamp) - parseTimestamp(b.timestamp));
  const inputsSummary: ConformanceReportSummary['inputs'] = [];

  for (const run of sortedRuns) {
    const { result } = run;
    const overall = result.overall as VerificationStatus;
    if (overall && Object.prototype.hasOwnProperty.call(statusBreakdown, overall)) {
      statusBreakdown[overall] += 1;
    }

    totals.rulesExecuted += result.summary?.rulesExecuted ?? 0;
    totals.rulesPassed += result.summary?.rulesPassed ?? 0;
    totals.rulesFailed += result.summary?.rulesFailed ?? 0;
    totals.rulesErrored += result.summary?.rulesError ?? 0;
    totals.rulesSkipped += result.summary?.rulesSkipped ?? 0;
    totals.totalViolations += result.violations?.length ?? 0;

    for (const severity of VIOLATION_SEVERITIES) {
      const value = result.summary?.violationsBySeverity?.[severity] ?? 0;
      severityTotals[severity] += value;
    }

    for (const category of CONFORMANCE_CATEGORIES) {
      const value = result.summary?.violationsByCategory?.[category] ?? 0;
      categoryTotals[category] += value;
    }

    result.results?.forEach((res) => {
      if (res?.ruleId) {
        uniqueRules.add(res.ruleId);
      }
    });

    result.violations?.forEach((violation) => {
      if (violation.ruleId) {
        uniqueViolationRules.add(violation.ruleId);
      }

      const key = violation.ruleId ?? `${violation.ruleName}:${violation.message}`;
      if (!key) return;

      const lastObserved = getViolationLastObserved(violation, run.timestamp);
      const existing = violationAccumulator.get(key);
      if (existing) {
        existing.count += 1;
        if (lastObserved && (!existing.lastObserved || lastObserved > existing.lastObserved)) {
          existing.lastObserved = lastObserved;
        }
      } else {
        violationAccumulator.set(key, {
          ruleId: violation.ruleId,
          ruleName: violation.ruleName ?? violation.ruleId ?? 'unknown',
          count: 1,
          lastObserved,
        });
      }
    });

    inputsSummary.push({
      file: run.file,
      timestamp: run.timestamp,
      status: overall,
      environment: result.metadata?.environment ?? 'unknown',
      version: result.metadata?.version ?? 'unknown',
      totalViolations: result.violations?.length ?? 0,
    });
  }

  if (failedFiles.length > 0) {
    const now = new Date().toISOString();
    for (const failed of failedFiles) {
      statusBreakdown.error += 1;
      inputsSummary.push({
        file: failed,
        timestamp: now,
        status: 'error',
        environment: 'unknown',
        version: 'unknown',
        totalViolations: 0,
      });
    }
  }

  totals.uniqueRules = uniqueRules.size;
  totals.uniqueViolationRules = uniqueViolationRules.size;

  const latestRun = sortedRuns[sortedRuns.length - 1];
  const previousRun = sortedRuns.length > 1 ? sortedRuns[sortedRuns.length - 2] : undefined;

  const severityTrends = VIOLATION_SEVERITIES.map((severity) => {
    const current = latestRun?.result.summary?.violationsBySeverity?.[severity] ?? 0;
    const previous = previousRun?.result.summary?.violationsBySeverity?.[severity] ?? 0;
    let trend: 'increasing' | 'decreasing' | 'stable' = 'stable';
    if (current > previous) {
      trend = 'increasing';
    } else if (current < previous) {
      trend = 'decreasing';
    }
    return { severity, current, previous, trend };
  });

  const status: ConformanceReportStatus =
    statusBreakdown.fail > 0 || statusBreakdown.error > 0 || statusBreakdown.timeout > 0 ? 'failure' : 'success';

  const topViolations = Array.from(violationAccumulator.values())
    .sort((a, b) => {
      if (b.count !== a.count) {
        return b.count - a.count;
      }
      const aTime = a.lastObserved ? parseTimestamp(a.lastObserved) : 0;
      const bTime = b.lastObserved ? parseTimestamp(b.lastObserved) : 0;
      return bTime - aTime;
    })
    .slice(0, 10);

  const summary: ConformanceReportSummary = {
    schemaVersion: REPORT_SCHEMA_VERSION,
    generatedAt,
    status,
    runsAnalyzed: runs.length,
    statusBreakdown,
    totals,
    severityTotals,
    categoryTotals,
    severityTrends,
    topViolations,
    inputs: inputsSummary,
  };

  if (latestRun) {
    summary.latestRun = {
      file: latestRun.file,
      timestamp: latestRun.timestamp,
      status: latestRun.result.overall,
      environment: latestRun.result.metadata?.environment ?? 'unknown',
      version: latestRun.result.metadata?.version ?? 'unknown',
      rulesExecuted: latestRun.result.summary?.rulesExecuted ?? 0,
      rulesFailed: latestRun.result.summary?.rulesFailed ?? 0,
      totalViolations: latestRun.result.violations?.length ?? 0,
    };
  }

  if (status === 'failure') {
    summary.notes = 'One or more runs reported failures, errors, or timeouts.';
  }

  if (failedFiles.length > 0) {
    const failureNote = `Failed to load ${failedFiles.length} conformance result file(s).`;
    summary.notes = summary.notes ? `${summary.notes} ${failureNote}` : failureNote;
  }

  return summary;
}

export function renderConformanceMarkdown(summary: ConformanceReportSummary): string {
  const lines: string[] = [
    '# Conformance Summary',
    `- Generated: ${summary.generatedAt}`,
    `- Status: ${summary.status}`,
    `- Runs Analyzed: ${summary.runsAnalyzed}`,
    '',
  ];

  lines.push('## Totals');
  lines.push(`- Total Violations: ${summary.totals.totalViolations}`);
  lines.push(`- Rules Failed: ${summary.totals.rulesFailed}`);
  lines.push(`- Rules Passed: ${summary.totals.rulesPassed}`);
  lines.push(`- Rules Skipped: ${summary.totals.rulesSkipped}`);
  lines.push(`- Unique Rules Checked: ${summary.totals.uniqueRules}`);
  lines.push(`- Unique Violating Rules: ${summary.totals.uniqueViolationRules}`);
  lines.push('');

  lines.push('## Severity Trends');
  lines.push('| Severity | Current | Previous | Trend |');
  lines.push('| --- | --- | --- | --- |');
  for (const trend of summary.severityTrends) {
    lines.push(`| ${trend.severity} | ${trend.current} | ${trend.previous} | ${trend.trend} |`);
  }
  lines.push('');

  if (summary.topViolations.length > 0) {
    lines.push('## Top Violations');
    lines.push('| Rule | Count | Last Observed |');
    lines.push('| --- | --- | --- |');
    for (const violation of summary.topViolations) {
      lines.push(`| ${violation.ruleName || violation.ruleId} | ${violation.count} | ${violation.lastObserved ?? 'n/a'} |`);
    }
    lines.push('');
  } else {
    lines.push('## Top Violations');
    lines.push('No recurring violations detected.');
    lines.push('');
  }

  lines.push('## Runs');
  if (summary.inputs.length === 0) {
    lines.push('No conformance runs were discovered.');
  } else {
    lines.push('| File | Status | Violations | Timestamp |');
    lines.push('| --- | --- | --- | --- |');
    for (const run of summary.inputs) {
      lines.push(`| ${run.file} | ${run.status} | ${run.totalViolations} | ${run.timestamp} |`);
    }
  }

  if (summary.latestRun) {
    lines.push('');
    lines.push('## Latest Run');
    lines.push(`- File: ${summary.latestRun.file}`);
    lines.push(`- Status: ${summary.latestRun.status}`);
    lines.push(`- Environment: ${summary.latestRun.environment}`);
    lines.push(`- Version: ${summary.latestRun.version}`);
    lines.push(`- Rules Executed: ${summary.latestRun.rulesExecuted}`);
    lines.push(`- Rules Failed: ${summary.latestRun.rulesFailed}`);
    lines.push(`- Violations: ${summary.latestRun.totalViolations}`);
  }

  if (summary.notes) {
    lines.push('');
    lines.push(`_Notes_: ${summary.notes}`);
  }

  return lines.join('\n');
}

export function toRelativePath(filePath: string): string {
  const relative = path.relative(process.cwd(), filePath);
  if (!relative || relative.startsWith('..')) {
    return filePath;
  }
  return relative;
}

function looksLikeGlob(value: string): boolean {
  return /[*?[\]]/.test(value);
}

function resolveResultTimestamp(result: ConformanceVerificationResult, filePath: string): string {
  if (result?.metadata?.timestamp) {
    return result.metadata.timestamp;
  }

  try {
    const stats = statSync(filePath);
    return stats.mtime.toISOString();
  } catch {
    return new Date().toISOString();
  }
}

function parseTimestamp(value: string): number {
  const parsed = Date.parse(value);
  return Number.isNaN(parsed) ? 0 : parsed;
}

function createEmptySeverityMap(): Record<ViolationSeverity, number> {
  return VIOLATION_SEVERITIES.reduce((acc, severity) => {
    acc[severity] = 0;
    return acc;
  }, {} as Record<ViolationSeverity, number>);
}

function createEmptyCategoryMap(): Record<ConformanceRuleCategory, number> {
  return CONFORMANCE_CATEGORIES.reduce((acc, category) => {
    acc[category] = 0;
    return acc;
  }, {} as Record<ConformanceRuleCategory, number>);
}

function getViolationLastObserved(violation: ViolationDetails, fallback: string): string | null {
  const timestamp = violation.context?.timestamp;
  if (timestamp && !Number.isNaN(Date.parse(timestamp))) {
    return timestamp;
  }
  if (fallback && !Number.isNaN(Date.parse(fallback))) {
    return fallback;
  }
  return null;
}
