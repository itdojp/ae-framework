import { describe, expect, it } from 'vitest';
import {
  evaluateModelCheckEnforcement,
  validateModelCheckReportContract,
} from '../../../scripts/verify/enforce-model-check-report.mjs';

const producer = {
  id: 'ae.formal.run-model-checks',
  version: '1.0.0',
  contract: 'formal-runner-result/v1',
  artifactRef: 'scripts/verify/run-model-checks.mjs',
};

function evidence({
  input,
  logPath,
  status = 'ok',
  code = 0,
  version = '2.20.0',
  versionStatus = 'verified',
  versionSource,
}: {
  input: string | string[];
  logPath: string;
  status?: 'ok' | 'failed' | 'timeout' | 'tool-error';
  code?: number | null;
  version?: string;
  versionStatus?: 'verified' | 'unknown' | 'mismatch';
  versionSource?: 'cli' | 'jar-manifest' | 'package-manifest' | 'reviewed-pin' | 'unavailable';
}) {
  const inputs = Array.isArray(input) ? input : [input];
  const specification = inputs[0];
  return {
    schemaVersion: 'formal-runner-result/v1',
    artifactStatus: 'execution-report',
    producer,
    provenance: 'runner-reported',
    executionOccurred: true,
    verificationKind: 'model-check',
    tool: {
      name: specification.endsWith('.als') ? 'Alloy' : 'TLC',
      version,
      versionStatus,
      versionSource: versionSource ?? (versionStatus === 'verified' ? 'cli' : 'unavailable'),
    },
    input: inputs,
    result: { status, code, logPath },
    scope: `Verification scope for ${inputs.join(', ')}`,
    assumptions: ['Only the supplied input and declared bounds are covered.'],
  };
}

function tlcResult(overrides: Record<string, unknown> = {}) {
  return {
    module: 'Safe',
    ok: true,
    code: 0,
    log: 'artifacts/codex/Safe.tlc.log.txt',
    config: 'spec/formal/Safe.cfg',
    executionStatus: 'executed',
    evidence: evidence({
      input: ['spec/formal/Safe.tla', 'spec/formal/Safe.cfg'],
      logPath: 'artifacts/codex/Safe.tlc.log.txt',
    }),
    ...overrides,
  };
}

function alloyResult(overrides: Record<string, unknown> = {}) {
  return {
    file: 'spec/formal/Safe.als',
    ok: true,
    code: 0,
    signal: null,
    timeout: false,
    log: 'artifacts/codex/Safe.alloy.log.txt',
    executionStatus: 'executed',
    evidence: evidence({
      input: 'spec/formal/Safe.als',
      logPath: 'artifacts/codex/Safe.alloy.log.txt',
      version: '6.2.0',
    }),
    ...overrides,
  };
}

function report(overrides: Record<string, any> = {}) {
  const base = {
    schemaVersion: 'model-check-report/v1',
    artifactStatus: 'execution-report',
    status: 'executed',
    ok: true,
    generatedAtUtc: '2026-07-22T00:00:00.000Z',
    producer,
    detectedInputs: 2,
    executedInputs: 2,
    skippedInputs: 0,
    approvedSkipRefs: [],
    tlc: { results: [tlcResult()], skipped: [], errors: [] },
    alloy: { results: [alloyResult()], skipped: [], errors: [] },
  };
  return { ...base, ...overrides };
}

describe('enforce-formal model-check report', () => {
  it('accepts a complete all-pass report', () => {
    const payload = report();
    expect(validateModelCheckReportContract(payload)).toEqual([]);
    expect(evaluateModelCheckEnforcement(payload)).toEqual([]);
  });

  it.each([
    ['one pass plus one no-config skip', report({
      detectedInputs: 2,
      executedInputs: 1,
      skippedInputs: 1,
      tlc: { results: [tlcResult()], skipped: ['spec/formal/NoConfig.tla: no .cfg found'], errors: [] },
      alloy: { results: [], skipped: [], errors: [] },
    })],
    ['TLC pass plus all Alloy skipped', report({
      detectedInputs: 2,
      executedInputs: 1,
      skippedInputs: 1,
      tlc: { results: [tlcResult()], skipped: [], errors: [] },
      alloy: { results: [], skipped: ['spec/formal/Safe.als: no Alloy jar available'], errors: [] },
    })],
    ['only skipped', report({
      status: 'not-run', ok: null, detectedInputs: 1, executedInputs: 0, skippedInputs: 1,
      tlc: { results: [], skipped: ['spec/formal/NoConfig.tla: no .cfg found'], errors: [] },
      alloy: { results: [], skipped: [], errors: [] },
    })],
    ['reviewed skip request when exceptions are unsupported', report({
      detectedInputs: 2,
      executedInputs: 1,
      skippedInputs: 1,
      approvedSkipRefs: ['SEC-123'],
      tlc: { results: [tlcResult()], skipped: ['spec/formal/NoConfig.tla: SEC-123'], errors: [] },
      alloy: { results: [], skipped: [], errors: [] },
    })],
  ])('rejects %s', (_name, payload) => {
    expect(validateModelCheckReportContract(payload)).toEqual([]);
    expect(evaluateModelCheckEnforcement(payload).length).toBeGreaterThan(0);
  });

  it('rejects only tool-error while retaining the attempted execution record', () => {
    const failed = tlcResult({
      ok: false,
      code: null,
      executionStatus: 'tool-error',
      error: 'spawn java failed',
      evidence: evidence({
        input: ['spec/formal/Safe.tla', 'spec/formal/Safe.cfg'],
        logPath: 'artifacts/codex/Safe.tlc.log.txt',
        status: 'tool-error',
        code: null,
      }),
    });
    const payload = report({
      status: 'tool-error', ok: null, detectedInputs: 1, executedInputs: 0,
      tlc: { results: [failed], skipped: [], errors: [] },
      alloy: { results: [], skipped: [], errors: [] },
    });
    expect(validateModelCheckReportContract(payload)).toEqual([]);
    expect(evaluateModelCheckEnforcement(payload).join('\n')).toContain('actual checker execution');
  });

  it('rejects only timeout while retaining a timeout record', () => {
    const timedOut = alloyResult({
      ok: false,
      code: null,
      timeout: true,
      executionStatus: 'timeout',
      evidence: evidence({
        input: 'spec/formal/Safe.als',
        logPath: 'artifacts/codex/Safe.alloy.log.txt',
        status: 'timeout',
        code: null,
        version: '6.2.0',
      }),
    });
    const payload = report({
      status: 'failed', ok: false, detectedInputs: 1, executedInputs: 0,
      tlc: { results: [], skipped: [], errors: [] },
      alloy: { results: [timedOut], skipped: [], errors: [] },
    });
    expect(validateModelCheckReportContract(payload)).toEqual([]);
    expect(evaluateModelCheckEnforcement(payload).join('\n')).toContain('all-pass');
  });

  it.each([
    ['unknown', 'unknown'],
    ['mismatch', '6.2.0'],
  ] as const)('rejects %s tool-version provenance without deleting the execution', (versionStatus, version) => {
    const result = alloyResult({
      evidence: evidence({
        input: 'spec/formal/Safe.als',
        logPath: 'artifacts/codex/Safe.alloy.log.txt',
        version,
        versionStatus,
      }),
    });
    const payload = report({
      detectedInputs: 1,
      executedInputs: 1,
      tlc: { results: [], skipped: [], errors: [] },
      alloy: { results: [result], skipped: [], errors: [] },
    });
    expect(validateModelCheckReportContract(payload)).toEqual([]);
    expect(payload.alloy.results[0].evidence.executionOccurred).toBe(true);
    expect(evaluateModelCheckEnforcement(payload).join('\n')).toContain('tool-version provenance');
  });

  it('rejects verified tool versions whose source is unavailable', () => {
    const result = alloyResult({
      evidence: evidence({
        input: 'spec/formal/Safe.als',
        logPath: 'artifacts/codex/Safe.alloy.log.txt',
        version: '6.2.0',
        versionStatus: 'verified',
        versionSource: 'unavailable',
      }),
    });
    const payload = report({
      detectedInputs: 1,
      executedInputs: 1,
      tlc: { results: [], skipped: [], errors: [] },
      alloy: { results: [result], skipped: [], errors: [] },
    });
    expect(validateModelCheckReportContract(payload).join('\n')).toContain('contradictory or incomplete');
    expect(evaluateModelCheckEnforcement(payload).length).toBeGreaterThan(0);
  });
});
