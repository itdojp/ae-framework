import { describe, expect, it } from 'vitest';
import { chmodSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { dirname, join, resolve } from 'node:path';

const repoRoot = resolve('.');
const localTmpRoot = resolve(repoRoot, '.codex-local/tmp');
const tlaRunner = resolve(repoRoot, 'scripts/formal/verify-tla.mjs');
const alloyRunner = resolve(repoRoot, 'scripts/formal/verify-alloy.mjs');
const summaryGenerator = resolve(repoRoot, 'scripts/formal/generate-formal-summary-v1.mjs');
const assuranceAggregator = resolve(repoRoot, 'scripts/assurance/aggregate-lanes.mjs');

function write(target: string, content: string) {
  mkdirSync(dirname(target), { recursive: true });
  writeFileSync(target, content, 'utf8');
}

function run(cwd: string, script: string, args: string[], env: NodeJS.ProcessEnv = {}) {
  return spawnSync(process.execPath, [script, ...args], {
    cwd,
    encoding: 'utf8',
    env: { ...process.env, ...env },
  });
}

describe('actual formal runner to Assurance evidence', () => {
  it('promotes schema-valid TLC and Alloy runner outputs through Formal Summary', () => {
    mkdirSync(localTmpRoot, { recursive: true });
    const sandbox = mkdtempSync(join(localTmpRoot, 'formal-runner-assurance-e2e-'));
    try {
      write(join(sandbox, 'spec/tla/DomainSpec.tla'), '---- MODULE DomainSpec ----\nVARIABLE x\nInvariant == x >= 0\n====\n');
      write(join(sandbox, 'spec/alloy/Domain.als'), 'sig Item {}\nrun {} for 1\n');
      write(join(sandbox, 'tools/tla2tools.jar'), 'fixture-tla-jar');
      write(join(sandbox, 'tools/alloy.jar'), 'fixture-alloy-jar');
      const fakeBin = join(sandbox, 'fake-bin');
      const fakeJava = join(fakeBin, 'java');
      write(fakeJava, `#!/bin/sh
case "$*" in
  *"tlc2.TLC -version"*) printf '%s\\n' 'TLC2 Version 2.20.0';;
  *"tlc2.TLC"*) printf '%s\\n' 'Model checking completed. No error has been found.';;
  *"alloy.jar version"*) printf '%s\\n' 'Alloy 6.2.0';;
  *"alloy.jar exec"*) printf '%s\\n' 'Alloy execution completed without a counterexample.';;
  *) printf '%s\\n' 'OpenJDK 17.0.12';;
esac
exit 0
`);
      chmodSync(fakeJava, 0o755);
      const env = {
        PATH: `${fakeBin}:/usr/bin:/bin`,
        TLA_TOOLS_JAR: join(sandbox, 'tools/tla2tools.jar'),
        ALLOY_JAR: join(sandbox, 'tools/alloy.jar'),
        GIT_COMMIT: '0123456789abcdef0123456789abcdef01234567',
      };

      const tla = run(sandbox, tlaRunner, ['--engine=tlc', '--file=spec/tla/DomainSpec.tla'], env);
      expect(tla.status, tla.stderr || tla.stdout).toBe(0);
      const alloy = run(sandbox, alloyRunner, ['--file=spec/alloy/Domain.als'], env);
      expect(alloy.status, alloy.stderr || alloy.stdout).toBe(0);

      const tlaRaw = JSON.parse(readFileSync(join(sandbox, 'artifacts/hermetic-reports/formal/tla-summary.json'), 'utf8'));
      const alloyRaw = JSON.parse(readFileSync(join(sandbox, 'artifacts/hermetic-reports/formal/alloy-summary.json'), 'utf8'));
      expect(tlaRaw.runnerResult).toMatchObject({
        schemaVersion: 'formal-runner-output/v1',
        contractId: 'formal-runner-output.v1',
        producer: { id: 'ae.formal.verify-tla' },
        executionEvidence: {
          artifactStatus: 'execution-report',
          producer: { id: 'ae.formal.verify-tla' },
          provenance: 'runner-reported',
          executionOccurred: true,
          verificationKind: 'model-check',
          tool: { version: '2.20.0', versionStatus: 'verified', versionSource: 'cli' },
          result: { status: 'ok', code: 0 },
        },
      });
      expect(alloyRaw.runnerResult).toMatchObject({
        schemaVersion: 'formal-runner-output/v1',
        contractId: 'formal-runner-output.v1',
        producer: { id: 'ae.formal.verify-alloy' },
        executionEvidence: {
          artifactStatus: 'execution-report',
          producer: { id: 'ae.formal.verify-alloy' },
          provenance: 'runner-reported',
          executionOccurred: true,
          verificationKind: 'model-check',
          tool: { version: '6.2.0', versionStatus: 'verified', versionSource: 'cli' },
          result: { status: 'ok', code: 0 },
        },
      });

      const formalV2 = join(sandbox, 'artifacts/formal/formal-summary-v2.json');
      const generated = run(sandbox, summaryGenerator, [
        '--layout', 'hermetic',
        '--in', 'artifacts/hermetic-reports',
        '--out', 'artifacts/formal/formal-summary-v1.json',
        '--out-v2', formalV2,
      ], env);
      expect(generated.status, generated.stderr || generated.stdout).toBe(0);
      const formalSummary = JSON.parse(readFileSync(formalV2, 'utf8'));
      const byName = Object.fromEntries(formalSummary.results.map((entry: any) => [entry.name, entry]));
      expect(byName.tla.status).toBe('ok');
      expect(byName.alloy.status).toBe('ok');
      expect(byName.tla.executionEvidence).toMatchObject({
        provenance: 'adapter-verified',
        adapter: { id: 'ae.formal.summary-generator' },
      });

      const profile = join(sandbox, 'assurance-profile.json');
      write(profile, JSON.stringify({
        schemaVersion: 'assurance-profile/v1',
        profileId: 'actual-runner-e2e',
        claims: [{
          id: 'formal-runner-executed',
          statement: 'Reviewed formal runners executed for the declared inputs.',
          criticality: 'high',
          targetLevel: 'A2',
          minIndependentSources: 1,
          requiredLanes: ['model'],
          requiredEvidenceKinds: ['model-check'],
        }],
      }, null, 2));
      const assuranceOut = join(sandbox, 'artifacts/assurance/assurance-summary.json');
      const aggregated = run(sandbox, assuranceAggregator, [
        '--assurance-profile', profile,
        '--formal-summary', formalV2,
        '--generated-at', '2026-07-22T00:00:00.000Z',
        '--output-json', assuranceOut,
        '--output-md', join(sandbox, 'artifacts/assurance/assurance-summary.md'),
      ], env);
      expect(aggregated.status, aggregated.stderr || aggregated.stdout).toBe(0);
      const assurance = JSON.parse(readFileSync(assuranceOut, 'utf8'));
      expect(assurance.claims[0]).toMatchObject({
        claimId: 'formal-runner-executed',
        observedLanes: ['model'],
        observedEvidenceKinds: ['model-check'],
      });
      expect(assurance.laneCoverage.model.observedClaims).toBe(1);
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });
});
