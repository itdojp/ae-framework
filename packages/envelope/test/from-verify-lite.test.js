import { describe, expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import { fromVerifyLite } from '../src/from-verify-lite.js';
import { fileURLToPath } from 'node:url';
const fixturePath = fileURLToPath(new URL('../__fixtures__/verify-lite-summary.json', import.meta.url));
const loadSummary = () => JSON.parse(readFileSync(fixturePath, 'utf8'));

describe('fromVerifyLite', () => {
  it('converts a verify lite summary into an envelope structure', () => {
    const summary = loadSummary();
    const envelope = fromVerifyLite(summary, {
      correlation: {
        runId: '18268371063',
        workflow: 'Verify Lite',
        commit: '01a5c13d',
        branch: 'refs/heads/main',
      },
      tempoLinkTemplate: 'https://tempo.example.com/explore?traceId={traceId}',
      notes: ['First note'],
      extraArtifacts: [
        { type: 'application/json', path: 'reports/conformance/extra.json', description: 'Extra' },
      ],
    });

    expect(envelope.schemaVersion).toBe('1.0.0');
    expect(envelope.source).toBe('verify-lite');
    expect(envelope.traceCorrelation).toMatchObject({
      runId: '18268371063',
      workflow: 'Verify Lite',
      commit: '01a5c13d',
      branch: 'refs/heads/main',
    });
    expect(envelope.correlation).toMatchObject({
      runId: '18268371063',
      workflow: 'Verify Lite',
      commit: '01a5c13d',
      branch: 'refs/heads/main',
    });
    expect(envelope.artifacts.map((item) => item.path)).toEqual([
      'verify-lite-lint-summary.json',
      'reports/mutation/summary.json',
      'reports/mutation/survivors.json',
      'reports/conformance/verify-lite-summary.json',
      'reports/conformance/extra.json',
    ]);
    expect(envelope.tempoLinks).toContain('https://tempo.example.com/explore?traceId=inventory-trace');
    expect(envelope.notes).toContain('First note');
    expect(envelope.notes).toContain('Tempo: https://tempo.example.com/explore?traceId=inventory-trace');

    // Ensure original summary is not mutated
    expect(summary.trace?.traceIds).toEqual(['trace-1']);
    expect(summary.tempoLinks).toEqual(['https://tempo.example.com/explore?traceId=summary-trace']);
  });

  it('handles missing artifacts and injects trace ids when absent', () => {
    const summary = loadSummary();
    delete summary.artifacts.mutationSummary;
    if (summary.trace) {
      delete summary.trace.traceIds;
    }

    const envelope = fromVerifyLite(summary, {
      correlation: { runId: '1' },
      tempoLinks: ['https://tempo.example.com/explore?traceId=external'],
    });

    expect(envelope.artifacts.map((item) => item.path)).not.toContain('reports/mutation/summary.json');
    expect(envelope.traceCorrelation.traceIds).toContain('inventory-trace');
    expect(envelope.summary.trace?.traceIds).toContain('inventory-trace');
    expect(envelope.tempoLinks).toContain('https://tempo.example.com/explore?traceId=external');
  });

  it('includes context-pack phase5 report artifacts when present in summary', () => {
    const summary = loadSummary();
    summary.artifacts.contextPackPhase5ReportJson = 'artifacts/context-pack/context-pack-phase5-report.json';
    summary.artifacts.contextPackPhase5ReportMarkdown = 'artifacts/context-pack/context-pack-phase5-report.md';

    const envelope = fromVerifyLite(summary, {
      correlation: { runId: 'phase5-run' },
    });

    const artifactPaths = envelope.artifacts.map((item) => item.path);
    expect(artifactPaths).toContain('artifacts/context-pack/context-pack-phase5-report.json');
    expect(artifactPaths).toContain('artifacts/context-pack/context-pack-phase5-report.md');
  });
});
