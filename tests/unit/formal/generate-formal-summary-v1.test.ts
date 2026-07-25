import { describe, expect, it } from 'vitest';
import { mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';

const generatorScript = resolve('scripts/formal/generate-formal-summary-v1.mjs');
const producerRefs: Record<string, string> = {
  alloy: 'scripts/formal/verify-alloy.mjs',
  apalache: 'scripts/formal/verify-apalache.mjs',
  conformance: 'scripts/formal/verify-conformance.mjs',
  csp: 'scripts/formal/verify-csp.mjs',
};

function executionEvidence(runner: string, input: string, logPath: string, toolName = runner) {
  return {
    schemaVersion: 'formal-runner-result/v1',
    artifactStatus: 'execution-report',
    producer: {
      id: `ae.formal.verify-${runner}`,
      version: '1.0.0',
      contract: 'formal-runner-result/v1',
      artifactRef: producerRefs[runner],
    },
    provenance: 'runner-reported',
    executionOccurred: true,
    verificationKind: runner === 'conformance' ? 'conformance' : runner === 'csp' ? 'typecheck' : 'model-check',
    tool: { name: toolName, version: '6.2.0', versionStatus: 'verified', versionSource: 'cli' },
    input: [input],
    result: { status: 'ok', code: 0, logPath },
    scope: `Verification scope for ${input}`,
    assumptions: ['The declared verification bounds match the reviewed scope.'],
  };
}

function runnerResult(runner: string, evidence: any) {
  return {
    schemaVersion: 'formal-runner-output/v1',
    contractId: 'formal-runner-output.v1',
    artifactStatus: evidence.artifactStatus,
    producer: {
      id: `ae.formal.verify-${runner}`,
      version: '1.0.0',
      contract: 'formal-runner-result/v1',
      artifactRef: producerRefs[runner],
    },
    executionEvidence: evidence,
  };
}

function writeJson(p: string, data: unknown) {
  mkdirSync(dirname(p), { recursive: true });
  writeFileSync(p, JSON.stringify(data, null, 2), 'utf8');
}

function runNode(cwd: string, args: string[], env: Record<string, string>) {
  return spawnSync('node', [generatorScript, ...args], {
    cwd,
    encoding: 'utf8',
    env: { ...process.env, ...env },
  });
}

describe('formal-summary/v1 generator', () => {
  it('supports hermetic layout inputs', () => {
    const dir = mkdtempSync(join(tmpdir(), 'formal-summary-v1-'));
    try {
      const commit = '0123456789abcdef0123456789abcdef01234567';

      writeJson(join(dir, 'input', 'formal', 'tla-summary.json'), { ran: true, status: 'ran' });
      writeFileSync(join(dir, 'input', 'formal', 'tla-output.txt'), 'tla output\n', 'utf8');
      writeJson(join(dir, 'input', 'formal', 'alloy-summary.json'), {
        ok: true,
        exitCode: 0,
        timeMs: 10,
        runnerResult: runnerResult('alloy', executionEvidence(
          'alloy',
          'spec/formal/model.als',
          'artifacts/formal/alloy-output.txt',
          'Alloy',
        )),
      });
      writeFileSync(join(dir, 'input', 'formal', 'alloy-output.txt'), 'alloy output\n', 'utf8');
      writeJson(join(dir, 'input', 'conformance', 'summary.json'), {
        ok: true,
        exitCode: 0,
        timeMs: 5,
        runnerResult: runnerResult('conformance', executionEvidence(
          'conformance',
          'samples/conformance/sample-traces.json',
          'artifacts/hermetic-reports/conformance/summary.json',
          'ae-framework conformance validator',
        )),
      });

      const out = join(dir, 'out', 'formal-summary-v1.json');
      const outV2 = join(dir, 'out', 'formal-summary-v2.json');
      const result = runNode(dir, ['--layout', 'hermetic', '--in', 'input', '--out', out, '--out-v2', outV2], { GIT_COMMIT: commit });
      expect(result.status).toBe(0);

      const payload = JSON.parse(readFileSync(out, 'utf8'));
      expect(payload.schemaVersion).toBe('formal-summary/v1');
      expect(payload.tool).toBe('aggregate');
      expect(payload.artifactStatus).toBe('execution-report');
      expect(payload.producer.id).toBe('ae.formal.summary-generator');
      expect(payload.metadata.gitCommit).toBe(commit);

      const payloadV2 = JSON.parse(readFileSync(outV2, 'utf8'));
      expect(payloadV2.schemaVersion).toBe('formal-summary/v2');
      expect(payloadV2.contractId).toBe('formal-summary.v2');
      expect(payloadV2.metadata.gitCommit).toBe(commit);

      const names = payload.results.map((r: any) => r.name);
      expect(names).toEqual(['tla', 'alloy', 'smt', 'apalache', 'conformance', 'kani', 'spin', 'csp', 'lean']);

      const byName = Object.fromEntries(payload.results.map((r: any) => [r.name, r]));
      expect(byName.alloy.status).toBe('ok');
      expect(byName.alloy.code).toBe(0);
      expect(byName.alloy.durationMs).toBe(10);
      expect(byName.alloy.executionEvidence).toMatchObject({
        schemaVersion: 'formal-runner-result/v1',
        artifactStatus: 'execution-report',
        provenance: 'adapter-verified',
        adapter: { id: 'ae.formal.summary-generator' },
        producer: { id: 'ae.formal.verify-alloy' },
        tool: { name: 'Alloy', version: '6.2.0', versionStatus: 'verified' },
        input: ['spec/formal/model.als'],
        result: { status: 'ok', code: 0, logPath: 'input/formal/alloy-output.txt' },
        scope: expect.stringContaining('model.als'),
        assumptions: ['The declared verification bounds match the reviewed scope.'],
      });

      expect(byName.conformance.status).toBe('ok');
      expect(byName.conformance.code).toBe(0);
      expect(byName.conformance.durationMs).toBe(5);
      expect(byName.conformance.executionEvidence.producer.id).toBe('ae.formal.verify-conformance');

      // ran without ok flag is normalized to unknown (fact-only)
      expect(byName.tla.status).toBe('unknown');
      expect(byName.tla.reason).toBe('ran_without_ok');
      expect(byName.tla.logPath).toBe('input/formal/tla-output.txt');
      expect(byName.alloy.logPath).toBe('input/formal/alloy-output.txt');

      // missing inputs still get an explicit result entry
      expect(byName.smt.status).toBe('missing');
      expect(byName.apalache.status).toBe('missing');
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  });

  it('supports downloaded layout inputs', () => {
    const dir = mkdtempSync(join(tmpdir(), 'formal-summary-v1-'));
    try {
      const commit = '0123456789abcdef0123456789abcdef01234567';

      // Simulate a downloaded artifacts layout (artifacts_dl/formal-reports-*/...).
      // raw.outputFile points to a hermetic path that might exist in the workspace; generator must prefer the downloaded log.
      writeJson(join(dir, 'input', 'formal-reports-apalache', 'apalache-summary.json'), {
        ok: true,
        exitCode: 0,
        timeMs: 12,
        outputFile: 'artifacts/hermetic-reports/formal/apalache-output.txt',
        runnerResult: runnerResult('apalache', executionEvidence(
          'apalache',
          'spec/tla/DomainSpec.tla',
          'artifacts/hermetic-reports/formal/apalache-output.txt',
          'Apalache',
        )),
      });
      writeFileSync(join(dir, 'input', 'formal-reports-apalache', 'apalache-output.txt'), 'downloaded log\n', 'utf8');

      // Workspace log with the same repo-relative path (should NOT be picked when baseDir is 'input').
      mkdirSync(join(dir, 'artifacts', 'hermetic-reports', 'formal'), { recursive: true });
      writeFileSync(join(dir, 'artifacts', 'hermetic-reports', 'formal', 'apalache-output.txt'), 'workspace log\n', 'utf8');

      const out = join(dir, 'out', 'formal-summary-v1.json');
      const result = runNode(dir, ['--layout', 'downloaded', '--in', 'input', '--out', out], { GIT_COMMIT: commit });
      expect(result.status).toBe(0);

      const payload = JSON.parse(readFileSync(out, 'utf8'));
      const byName = Object.fromEntries(payload.results.map((r: any) => [r.name, r]));
      expect(byName.apalache.status).toBe('ok');
      expect(byName.apalache.logPath).toBe('input/formal-reports-apalache/apalache-output.txt');
      expect(byName.apalache.executionEvidence.producer.id).toBe('ae.formal.verify-apalache');
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  });

  it.each([
    ['complete-looking legacy evidence', {
      provenance: 'runner-reported',
      tool: { name: 'Alloy', version: '6.2.0' },
      input: ['spec/formal/model.als'],
      result: { status: 'ok', code: 0, logPath: 'artifacts/formal/alloy-output.txt' },
      scope: 'Hand-authored scope',
      assumptions: ['Hand-authored assumption'],
    }],
    ['unknown producer', {
      ...executionEvidence('alloy', 'spec/formal/model.als', 'artifacts/formal/alloy-output.txt', 'Alloy'),
      producer: {
        id: 'ae.formal.fake-runner',
        version: '1.0.0',
        contract: 'formal-runner-result/v1',
        artifactRef: 'scripts/formal/fake-runner.mjs',
      },
    }],
    ['schema-invalid result code', {
      ...executionEvidence('alloy', 'spec/formal/model.als', 'artifacts/formal/alloy-output.txt', 'Alloy'),
      result: { status: 'ok', code: '0', logPath: 'artifacts/formal/alloy-output.txt' },
    }],
    ['synthetic artifact status', {
      ...executionEvidence('alloy', 'spec/formal/model.als', 'artifacts/formal/alloy-output.txt', 'Alloy'),
      artifactStatus: 'synthetic',
    }],
    ['traversing log path with a valid basename', {
      ...executionEvidence('alloy', 'spec/formal/model.als', 'artifacts/formal/alloy-output.txt', 'Alloy'),
      result: { status: 'ok', code: 0, logPath: '../../private/alloy-output.txt' },
    }],
    ['absolute log path with a valid basename', {
      ...executionEvidence('alloy', 'spec/formal/model.als', 'artifacts/formal/alloy-output.txt', 'Alloy'),
      result: { status: 'ok', code: 0, logPath: '/private/alloy-output.txt' },
    }],
    ['unsafe input path', {
      ...executionEvidence('alloy', 'spec/formal/model.als', 'artifacts/formal/alloy-output.txt', 'Alloy'),
      input: ['../private/model.als'],
    }],
  ])('does not promote %s', (_name, untrustedEvidence) => {
    const dir = mkdtempSync(join(tmpdir(), 'formal-summary-v1-untrusted-'));
    try {
      writeJson(join(dir, 'input', 'formal', 'alloy-summary.json'), {
        ok: true,
        exitCode: 0,
        runnerResult: runnerResult('alloy', untrustedEvidence),
      });
      const out = join(dir, 'out', 'formal-summary-v1.json');
      const result = runNode(dir, ['--layout', 'hermetic', '--in', 'input', '--out', out], {
        GIT_COMMIT: '0123456789abcdef0123456789abcdef01234567',
      });
      expect(result.status).toBe(0);
      const payload = JSON.parse(readFileSync(out, 'utf8'));
      const alloy = payload.results.find((entry: any) => entry.name === 'alloy');
      expect(alloy).toMatchObject({
        status: 'unknown',
        artifactStatus: 'not-executed',
        reason: 'invalid_runner_output_contract',
      });
      expect(alloy).not.toHaveProperty('executionEvidence');
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  });

  it('does not promote exact hand-authored runner-reported evidence without the reviewed output envelope', () => {
    const dir = mkdtempSync(join(tmpdir(), 'formal-summary-v1-forged-'));
    try {
      writeJson(join(dir, 'input', 'formal', 'alloy-summary.json'), {
        ok: true,
        exitCode: 0,
        executionEvidence: executionEvidence(
          'alloy',
          'spec/formal/model.als',
          'artifacts/formal/alloy-output.txt',
          'Alloy',
        ),
      });
      writeFileSync(join(dir, 'input', 'formal', 'alloy-output.txt'), 'forged output\n', 'utf8');
      const out = join(dir, 'out', 'formal-summary-v1.json');
      const result = runNode(dir, ['--layout', 'hermetic', '--in', 'input', '--out', out], {
        GIT_COMMIT: '0123456789abcdef0123456789abcdef01234567',
      });
      expect(result.status).toBe(0);
      const payload = JSON.parse(readFileSync(out, 'utf8'));
      const alloy = payload.results.find((entry: any) => entry.name === 'alloy');
      expect(alloy).toMatchObject({
        status: 'unknown',
        artifactStatus: 'not-executed',
        reason: 'runner_output_contract_missing',
      });
      expect(alloy).not.toHaveProperty('executionEvidence');
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  });

  it('does not let the CSP typecheck producer self-promote to model-check', () => {
    const dir = mkdtempSync(join(tmpdir(), 'formal-summary-v1-csp-kind-'));
    try {
      const evidence = executionEvidence(
        'csp',
        'spec/csp/cspx-smoke.cspm',
        'artifacts/hermetic-reports/formal/csp-output.txt',
        'cspx',
      );
      evidence.verificationKind = 'model-check';
      writeJson(join(dir, 'input', 'formal', 'csp-summary.json'), {
        ran: true,
        status: 'ran',
        ok: true,
        exitCode: 0,
        backend: 'cspx:typecheck',
        runnerResult: runnerResult('csp', evidence),
      });
      writeFileSync(join(dir, 'input', 'formal', 'csp-output.txt'), 'typecheck only\n', 'utf8');
      const out = join(dir, 'out', 'formal-summary-v1.json');
      const result = runNode(dir, ['--layout', 'hermetic', '--in', 'input', '--out', out], {
        GIT_COMMIT: '0123456789abcdef0123456789abcdef01234567',
      });
      expect(result.status).toBe(0);
      const payload = JSON.parse(readFileSync(out, 'utf8'));
      const csp = payload.results.find((entry: any) => entry.name === 'csp');
      expect(csp).toMatchObject({
        status: 'unknown',
        artifactStatus: 'not-executed',
        reason: 'invalid_runner_output_contract',
      });
      expect(csp).not.toHaveProperty('executionEvidence');
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  });

  it('preserves an execution attempt with unknown version but makes the result ineligible', () => {
    const dir = mkdtempSync(join(tmpdir(), 'formal-summary-v1-unknown-version-'));
    try {
      const unversioned = executionEvidence(
        'alloy',
        'spec/formal/model.als',
        'artifacts/formal/alloy-output.txt',
        'Alloy',
      );
      unversioned.tool = {
        ...unversioned.tool,
        version: 'unknown',
        versionStatus: 'unknown',
        versionSource: 'unavailable',
      };
      writeJson(join(dir, 'input', 'formal', 'alloy-summary.json'), {
        ok: true,
        exitCode: 0,
        runnerResult: runnerResult('alloy', unversioned),
      });
      writeFileSync(join(dir, 'input', 'formal', 'alloy-output.txt'), 'alloy output\n', 'utf8');
      const out = join(dir, 'out', 'formal-summary-v1.json');
      const result = runNode(dir, ['--layout', 'hermetic', '--in', 'input', '--out', out], {
        GIT_COMMIT: '0123456789abcdef0123456789abcdef01234567',
      });
      expect(result.status).toBe(0);
      const payload = JSON.parse(readFileSync(out, 'utf8'));
      const alloy = payload.results.find((entry: any) => entry.name === 'alloy');
      expect(alloy).toMatchObject({
        status: 'unknown',
        artifactStatus: 'execution-report',
        reason: 'tool_version_evidence_gap',
        executionEvidence: {
          executionOccurred: true,
          tool: { version: 'unknown', versionStatus: 'unknown' },
          result: { status: 'ok' },
        },
      });
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  });
});
