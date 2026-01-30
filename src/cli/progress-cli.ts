import { Command } from 'commander';
import chalk from 'chalk';
import fs from 'node:fs';
import path from 'node:path';
import { toMessage } from '../utils/error-utils.js';
import { safeExit } from '../utils/safe-exit.js';

type ProgressSummary = {
  generatedAt?: string;
  sources?: {
    metrics?: string | null;
    quality?: string | null;
    traceability?: string | null;
    phaseState?: string | null;
  };
  progress?: {
    currentPhase?: string | null;
    percent?: number;
    approvalsRequired?: boolean;
    phasesCompleted?: number;
    phasesTotal?: number;
  } | null;
  metrics?: {
    projectName?: string;
    sessionId?: string;
    tddCompliance?: number;
    overallCoverage?: number;
    totalViolations?: number;
    phasesCompleted?: number;
    phasesTotal?: number;
  } | null;
  quality?: {
    environment?: string;
    overallScore?: number;
    totalGates?: number;
    passedGates?: number;
    failedGates?: number;
    blockers?: string[];
    blocked?: boolean;
  } | null;
  traceability?: {
    total?: number;
    testsLinked?: number;
    implLinked?: number;
    formalLinked?: number;
    coverage?: {
      tests?: number;
      impl?: number;
      formal?: number;
    } | null;
  } | null;
  missing?: string[];
};

const DEFAULT_SUMMARY_PATH = path.join('artifacts', 'progress', 'summary.json');

const readSummary = (summaryPath: string): ProgressSummary => {
  const resolved = path.resolve(summaryPath);
  if (!fs.existsSync(resolved)) {
    throw new Error(`progress summary not found: ${summaryPath}`);
  }
  return JSON.parse(fs.readFileSync(resolved, 'utf8')) as ProgressSummary;
};

const formatPercent = (value?: number) => {
  if (typeof value !== 'number' || Number.isNaN(value)) return 'n/a';
  return `${Math.round(value)}%`;
};

const formatRatio = (value?: number) => {
  if (typeof value !== 'number' || Number.isNaN(value)) return 'n/a';
  return `${Math.round(value * 1000) / 10}%`;
};

const formatProgressLine = (progress: ProgressSummary['progress']) => {
  if (!progress) return null;
  const percent = typeof progress.percent === 'number' ? `${progress.percent}%` : 'n/a';
  const currentPhase = progress.currentPhase ?? 'n/a';
  const completed = progress.phasesCompleted ?? 0;
  const total = progress.phasesTotal ?? 0;
  return `Progress: ${percent} (phase=${currentPhase}, completed ${completed}/${total})`;
};

const formatQualityLine = (quality: ProgressSummary['quality']) => {
  if (!quality) return null;
  const env = quality.environment ?? 'n/a';
  const score = typeof quality.overallScore === 'number' ? quality.overallScore : 'n/a';
  const passed = quality.passedGates ?? 0;
  const total = quality.totalGates ?? 0;
  const blockers = Array.isArray(quality.blockers) ? quality.blockers.length : 0;
  return `Quality: ${env} score=${score} gates=${passed}/${total} blockers=${blockers}`;
};

const formatTraceabilityLine = (trace: ProgressSummary['traceability']) => {
  if (!trace) return null;
  const total = trace.total ?? 0;
  const tests = trace.coverage?.tests ?? null;
  const impl = trace.coverage?.impl ?? null;
  const formal = trace.coverage?.formal ?? null;
  return `Traceability: tests=${formatRatio(tests)} impl=${formatRatio(impl)} formal=${formatRatio(formal)} (total=${total})`;
};

const formatMetricsLine = (metrics: ProgressSummary['metrics']) => {
  if (!metrics) return null;
  const tdd = formatPercent(metrics.tddCompliance);
  const coverage = formatPercent(metrics.overallCoverage);
  const violations = metrics.totalViolations ?? 0;
  return `Metrics: TDD=${tdd} coverage=${coverage} violations=${violations}`;
};

const printStatus = (summary: ProgressSummary, includeTrace: boolean) => {
  const lines: string[] = [];
  const progressLine = formatProgressLine(summary.progress);
  if (progressLine) lines.push(progressLine);

  const qualityLine = formatQualityLine(summary.quality);
  if (qualityLine) lines.push(qualityLine);

  if (includeTrace) {
    const traceLine = formatTraceabilityLine(summary.traceability);
    if (traceLine) lines.push(traceLine);
  }

  const metricsLine = formatMetricsLine(summary.metrics);
  if (metricsLine) lines.push(metricsLine);

  if (lines.length === 0) {
    console.log('No progress summary available. Run `pnpm run progress:summary` first.');
    return;
  }

  for (const line of lines.slice(0, 4)) {
    console.log(line);
  }
};

const printBoard = (summary: ProgressSummary) => {
  console.log(chalk.bold('Progress Board'));
  console.log(`Generated: ${summary.generatedAt ?? 'n/a'}`);

  if (summary.progress) {
    const progress = summary.progress;
    console.log(`\nProgress: ${progress.percent ?? 'n/a'}%`);
    console.log(`- Current: ${progress.currentPhase ?? 'n/a'}`);
    console.log(`- Completed: ${progress.phasesCompleted ?? 0}/${progress.phasesTotal ?? 0}`);
    console.log(`- Approvals: ${progress.approvalsRequired ? 'required' : 'none'}`);
  } else {
    console.log('\nProgress: n/a');
  }

  if (summary.quality) {
    const quality = summary.quality;
    const blockers = Array.isArray(quality.blockers) ? quality.blockers : [];
    console.log(`\nQuality: ${quality.environment ?? 'n/a'} score=${quality.overallScore ?? 'n/a'}`);
    console.log(`- Gates: ${quality.passedGates ?? 0}/${quality.totalGates ?? 0}`);
    console.log(`- Blockers: ${blockers.length}`);
    if (blockers.length > 0) {
      blockers.slice(0, 5).forEach((blocker) => console.log(`  • ${blocker}`));
    }
  } else {
    console.log('\nQuality: n/a');
  }

  if (summary.metrics) {
    const metrics = summary.metrics;
    console.log(`\nMetrics: ${metrics.projectName ?? 'n/a'}`);
    console.log(`- Session: ${metrics.sessionId ?? 'n/a'}`);
    console.log(`- TDD: ${formatPercent(metrics.tddCompliance)}`);
    console.log(`- Coverage: ${formatPercent(metrics.overallCoverage)}`);
    console.log(`- Violations: ${metrics.totalViolations ?? 0}`);
  } else {
    console.log('\nMetrics: n/a');
  }

  if (summary.traceability) {
    const trace = summary.traceability;
    console.log(`\nTraceability: total=${trace.total ?? 0}`);
    console.log(`- Tests: ${trace.testsLinked ?? 0} (${formatRatio(trace.coverage?.tests)})`);
    console.log(`- Implementation: ${trace.implLinked ?? 0} (${formatRatio(trace.coverage?.impl)})`);
    console.log(`- Formal: ${trace.formalLinked ?? 0} (${formatRatio(trace.coverage?.formal)})`);
  } else {
    console.log('\nTraceability: n/a');
  }

  if (Array.isArray(summary.missing) && summary.missing.length > 0) {
    console.log(`\nMissing: ${summary.missing.join(', ')}`);
  }

  if (summary.sources) {
    console.log('\nSources:');
    const entries = Object.entries(summary.sources);
    for (const [key, value] of entries) {
      console.log(`- ${key}: ${value ?? 'n/a'}`);
    }
  }
};

export const createProgressCommands = (): Command[] => {
  const statusCommand = new Command('status')
    .description('Show overall progress status (2-4 lines)')
    .option('-s, --summary <path>', 'Progress summary JSON path', DEFAULT_SUMMARY_PATH)
    .option('--trace', 'Include traceability line')
    .action((options) => {
      try {
        const summary = readSummary(options.summary);
        printStatus(summary, Boolean(options.trace));
      } catch (error) {
        console.error(chalk.red(`❌ ${toMessage(error)}`));
        safeExit(1);
      }
    });

  const boardCommand = new Command('board')
    .description('Show detailed progress board')
    .option('-s, --summary <path>', 'Progress summary JSON path', DEFAULT_SUMMARY_PATH)
    .action((options) => {
      try {
        const summary = readSummary(options.summary);
        printBoard(summary);
      } catch (error) {
        console.error(chalk.red(`❌ ${toMessage(error)}`));
        safeExit(1);
      }
    });

  return [statusCommand, boardCommand];
};
