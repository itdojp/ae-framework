import { describe, expect, it } from 'vitest';
import {
  evaluateReadiness,
  formatPercent,
  isFailureConclusion,
  parseArgs,
} from '../../../scripts/ci/context-pack-gate-observability.mjs';

function baselineMetrics() {
  return {
    totalRuns: 30,
    successRuns: 28,
    failedRuns: 2,
    failureRatePercent: 6.67,
    meanDurationMinutes: 5.1,
    p95DurationMinutes: 8.3,
    mttr: {
      meanMinutes: 10,
      p95Minutes: 12,
      recoveries: 1,
      unresolvedFailureStreaks: 0,
    },
    reproductionRatePercent: 100,
    reproductionCandidates: 1,
    reproducedFailures: 1,
  };
}

describe('context-pack-gate-observability', () => {
  it('stops option parsing at --', () => {
    const options = parseArgs([
      'node',
      'scripts/ci/context-pack-gate-observability.mjs',
      '--repo',
      'itdojp/ae-framework',
      '--',
      '--unknown-option',
    ]);

    expect(options.repo).toBe('itdojp/ae-framework');
  });

  it('treats cancelled runs as non-failure', () => {
    expect(isFailureConclusion('cancelled')).toBe(false);
    expect(isFailureConclusion('failure')).toBe(true);
  });

  it('formats percent values without n/a%', () => {
    expect(formatPercent(12.3)).toBe('12.3%');
    expect(formatPercent(null)).toBe('n/a');
  });

  it('requires reproduction signal when failures exist', () => {
    const readiness = evaluateReadiness(
      {
        ...baselineMetrics(),
        failedRuns: 3,
        reproductionRatePercent: null,
        reproductionCandidates: 0,
        reproducedFailures: 0,
      },
      {
        minRuns: 20,
        failRatePercent: 20,
        reproductionRatePercent: 80,
        mttrMeanMinutes: 120,
      },
    );

    expect(readiness.readyForBlocking).toBe(false);
    expect(readiness.reasons.some((reason) => reason.includes('reproduction rate is n/a'))).toBe(true);
  });
});
