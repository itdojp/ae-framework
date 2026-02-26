import { describe, expect, it } from 'vitest';
import {
  buildHarnessHealthReport,
  collapseChecksByName,
  evaluateGateFromChecks,
  renderMarkdown,
} from '../../../scripts/ci/build-harness-health.mjs';

describe('build-harness-health', () => {
  it('deduplicates checks by workflow+name and keeps latest timestamp', () => {
    const checks = collapseChecksByName([
      {
        name: 'verify',
        workflowName: 'PR Verify',
        status: 'COMPLETED',
        conclusion: 'FAILURE',
        startedAt: '2026-02-25T00:00:00Z',
        completedAt: '2026-02-25T00:01:00Z',
      },
      {
        name: 'verify',
        workflowName: 'PR Verify',
        status: 'COMPLETED',
        conclusion: 'SUCCESS',
        startedAt: '2026-02-25T00:02:00Z',
        completedAt: '2026-02-25T00:03:00Z',
      },
    ]);

    expect(checks).toHaveLength(1);
    expect(checks[0]?.conclusion).toBe('SUCCESS');
  });

  it('marks gate as fail when at least one matched check is failed', () => {
    const gate = evaluateGateFromChecks(
      {
        id: 'example',
        title: 'Example Gate',
        matcher: (check) => check.name === 'verify',
      },
      [
        {
          name: 'verify',
          workflowName: 'PR Verify',
          status: 'COMPLETED',
          conclusion: 'FAILURE',
        },
      ],
    );

    expect(gate.status).toBe('fail');
    expect(gate.reasons[0]).toContain('Example Gate');
    expect(gate.reasons[0]).toContain('verify:FAILURE');
  });

  it('falls back to local artifacts and emits labels/hints on failures', () => {
    const report = buildHarnessHealthReport({
      repo: 'itdojp/ae-framework',
      prNumber: 2279,
      workflow: 'PR Maintenance',
      runId: 100,
      commitSha: 'abc123',
      checkRuns: [],
      labels: ['trace:TRACE-42', 'enforce-testing'],
      localArtifacts: {
        schemaValidation: { totals: { errorCount: 2 } },
        testingRepro: {
          records: [
            {
              status: 'fail',
              traceId: 'TRACE-100',
              seed: 20260226,
              reproducibleCommand: 'TRACE_ID=TRACE-100 pnpm run test:replay:focus --silent',
            },
          ],
        },
        contextPackDeps: { status: 'warn', violations: [{ id: 'CP-1' }] },
        heavyTrendSummary: { highestSeverity: 'critical' },
      },
      extraReasons: ['synthetic reason'],
    });

    expect(report.severity).toBe('critical');
    expect(report.gates.artifactsSchema.status).toBe('fail');
    expect(report.gates.testingHarness.status).toBe('fail');
    expect(report.gates.contextPack.status).toBe('warn');
    expect(report.gates.ciExtended.status).toBe('fail');
    expect(report.recommendedLabels).toContain('enforce-artifacts');
    expect(report.recommendedLabels).toContain('enforce-context-pack');
    expect(report.recommendedLabels).toContain('run-ci-extended');
    expect(report.recommendedLabels).not.toContain('enforce-testing');
    expect(report.reasons).toContain('synthetic reason');
    expect(report.reproducibleHints.some((hint) => hint.command?.includes('TRACE_ID=TRACE-42'))).toBe(true);
    expect(report.reproducibleHints.some((hint) => hint.seed === 20260226)).toBe(true);
  });

  it('renders detailed markdown with reasons and hints', () => {
    const markdown = renderMarkdown(
      {
        severity: 'warn',
        workflow: 'PR Maintenance',
        runId: 100,
        commitSha: 'abc123',
        gates: {
          artifactsSchema: { status: 'ok', checkCount: 1 },
          testingHarness: { status: 'warn', checkCount: 2 },
          contextPack: { status: 'skip', checkCount: 0 },
          ciExtended: { status: 'ok', checkCount: 1 },
        },
        reasons: ['Testing harness: pending checks'],
        recommendedLabels: ['enforce-testing'],
        reproducibleHints: [
          {
            gate: 'testingHarness',
            trace: 'TRACE-1',
            seed: 10,
            command: 'TRACE_ID=TRACE-1 pnpm run test:replay:focus --silent',
          },
        ],
      },
      'detailed',
    );

    expect(markdown).toContain('## Harness Health');
    expect(markdown).toContain('### Reasons');
    expect(markdown).toContain('### Reproducible Hints');
    expect(markdown).toContain('enforce-testing');
    expect(markdown).toContain('TRACE_ID=TRACE-1');
  });
});
