#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';

const cwd = process.cwd();

const readJson = (p) => {
  try {
    return JSON.parse(fs.readFileSync(p, 'utf8'));
  } catch {
    return undefined;
  }
};

const normalizePath = (p) => (p ? path.relative(cwd, p) : null);

const pickQualityReport = () => {
  const explicit = process.env.PROGRESS_QUALITY;
  if (explicit && fs.existsSync(explicit)) {
    return path.resolve(explicit);
  }

  const dir = path.join(cwd, 'reports', 'quality-gates');
  const preferred = [
    'quality-report-ci-latest.json',
    'quality-report-development-latest.json',
    'quality-report-production-latest.json',
  ];

  for (const filename of preferred) {
    const candidate = path.join(dir, filename);
    if (fs.existsSync(candidate)) {
      return candidate;
    }
  }

  if (!fs.existsSync(dir)) {
    return null;
  }

  const entries = fs
    .readdirSync(dir)
    .filter((file) => file.startsWith('quality-report-') && file.endsWith('.json'))
    .map((file) => path.join(dir, file));

  if (entries.length === 0) {
    return null;
  }

  entries.sort((a, b) => {
    const aTime = fs.statSync(a).mtimeMs;
    const bTime = fs.statSync(b).mtimeMs;
    return bTime - aTime;
  });

  return entries[0] ?? null;
};

const metricsPath = path.resolve(process.env.PROGRESS_METRICS ?? path.join(cwd, 'metrics', 'project-metrics.json'));
const traceabilityPath = path.resolve(process.env.PROGRESS_TRACEABILITY ?? path.join(cwd, 'traceability.json'));
const phaseStateRoot = process.env.AE_PHASE_STATE_ROOT;
const phaseStateFallback = phaseStateRoot
  ? path.join(path.resolve(phaseStateRoot), '.ae', 'phase-state.json')
  : path.join(cwd, '.ae', 'phase-state.json');
const phaseStatePath = path.resolve(
  process.env.PROGRESS_PHASE_STATE ?? process.env.AE_PHASE_STATE_FILE ?? phaseStateFallback
);
const qualityPath = pickQualityReport();
const outputPath = path.resolve(process.env.PROGRESS_SUMMARY_OUTPUT ?? path.join(cwd, 'artifacts', 'progress', 'summary.json'));

const metrics = fs.existsSync(metricsPath) ? readJson(metricsPath) : undefined;
const traceability = fs.existsSync(traceabilityPath) ? readJson(traceabilityPath) : undefined;
const phaseState = fs.existsSync(phaseStatePath) ? readJson(phaseStatePath) : undefined;
const quality = qualityPath && fs.existsSync(qualityPath) ? readJson(qualityPath) : undefined;

const phases = ['intent', 'formal', 'test', 'code', 'verify', 'operate'];
const phaseStatus = phaseState?.phaseStatus ?? {};
const completedCount = phases.filter((phase) => phaseStatus[phase]?.completed).length;
const progressPercent = phases.length > 0 ? Math.round((completedCount / phases.length) * 100) : 0;

const qualitySummary = quality
  ? {
      environment: quality.environment,
      overallScore: quality.overallScore,
      totalGates: quality.totalGates,
      passedGates: quality.passedGates,
      failedGates: quality.failedGates,
      blockers: quality.summary?.blockers ?? [],
      blocked: Array.isArray(quality.summary?.blockers) && quality.summary.blockers.length > 0,
    }
  : null;

const traceabilitySummary = traceability
  ? {
      total: traceability.total ?? 0,
      testsLinked: traceability.testsLinked ?? 0,
      implLinked: traceability.implLinked ?? 0,
      formalLinked: traceability.formalLinked ?? 0,
      coverage: traceability.total
        ? {
            tests: Number(((traceability.testsLinked ?? 0) / traceability.total).toFixed(3)),
            impl: Number(((traceability.implLinked ?? 0) / traceability.total).toFixed(3)),
            formal: Number(((traceability.formalLinked ?? 0) / traceability.total).toFixed(3)),
          }
        : null,
    }
  : null;

const metricsSummary = metrics
  ? {
      projectName: metrics.projectName,
      sessionId: metrics.sessionId,
      tddCompliance: metrics.tddCompliance,
      overallCoverage: metrics.overallCoverage,
      totalViolations: metrics.totalViolations,
      phasesCompleted: Array.isArray(metrics.phases) ? metrics.phases.filter((phase) => phase.endTime).length : 0,
      phasesTotal: Array.isArray(metrics.phases) ? metrics.phases.length : 0,
    }
  : null;

const summary = {
  generatedAt: new Date().toISOString(),
  sources: {
    metrics: metrics ? normalizePath(metricsPath) : null,
    quality: quality ? normalizePath(qualityPath) : null,
    traceability: traceability ? normalizePath(traceabilityPath) : null,
    phaseState: phaseState ? normalizePath(phaseStatePath) : null,
  },
  progress: phaseState
    ? {
        currentPhase: phaseState.currentPhase ?? null,
        percent: progressPercent,
        approvalsRequired: Boolean(phaseState.approvalsRequired),
        phasesCompleted: completedCount,
        phasesTotal: phases.length,
      }
    : null,
  metrics: metricsSummary,
  quality: qualitySummary,
  traceability: traceabilitySummary,
  missing: [],
};

summary.missing = Object.entries(summary.sources)
  .filter(([, value]) => !value)
  .map(([key]) => key);

fs.mkdirSync(path.dirname(outputPath), { recursive: true });
fs.writeFileSync(outputPath, JSON.stringify(summary, null, 2));
console.log(`✓ Wrote ${path.relative(cwd, outputPath)}`);
