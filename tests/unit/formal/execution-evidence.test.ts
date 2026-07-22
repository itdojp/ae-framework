import { describe, expect, it } from 'vitest';
import {
  buildFormalExecutionEvidence,
  buildFormalRunnerOutput,
  extractToolVersion,
  hasEligibleToolVersion,
  normalizeToolVersion,
} from '../../../scripts/formal/execution-evidence.mjs';

describe('formal execution evidence', () => {
  it.each([
    ['TLC2 Version 2.20.0', '2.20.0'],
    ['Alloy 6.2.0', '6.2.0'],
    ['Lean (version 4.19.0)', '4.19.0'],
    ['unknown', ''],
  ])('extracts a tool version from %s', (output, expected) => {
    expect(extractToolVersion(output)).toBe(expected);
  });

  it('keeps unknown version attempts but marks them ineligible', () => {
    const evidence = buildFormalExecutionEvidence({
      runner: 'tla',
      toolName: 'TLC',
      toolVersion: 'unknown',
      versionSource: 'unavailable',
      inputPaths: ['spec/tla/DomainSpec.tla'],
      resultStatus: 'ok',
      exitCode: 0,
      logPath: 'artifacts/formal/tla-output.txt',
      scope: 'TLC fixture scope',
      assumptions: ['The fixture scope is bounded.'],
      executionOccurred: true,
    });
    expect(evidence).toMatchObject({
      artifactStatus: 'execution-report',
      executionOccurred: true,
      tool: { version: 'unknown', versionStatus: 'unknown', versionSource: 'unavailable' },
      result: { status: 'ok', code: 0 },
    });
  });

  it('accepts known CLI versions and rejects reviewed artifact-pin mismatches', () => {
    expect(normalizeToolVersion({ version: '2.20.0', source: 'cli' })).toMatchObject({
      version: '2.20.0',
      versionStatus: 'verified',
    });
    expect(normalizeToolVersion({
      version: '6.2.0',
      source: 'reviewed-pin',
      artifactSha256: 'a'.repeat(64),
      expectedArtifactSha256: 'a'.repeat(64),
    })).toMatchObject({ versionStatus: 'verified' });
    expect(normalizeToolVersion({
      version: '6.2.0',
      source: 'reviewed-pin',
      artifactSha256: 'a'.repeat(64),
      expectedArtifactSha256: 'b'.repeat(64),
    })).toMatchObject({ versionStatus: 'mismatch' });
    expect(normalizeToolVersion({
      version: '6.2.0',
      source: 'cli',
      artifactSha256: 'a'.repeat(64),
      expectedArtifactSha256: 'b'.repeat(64),
    })).toMatchObject({ versionStatus: 'mismatch' });
  });

  it('binds runner-reported evidence to the closed runner output envelope', () => {
    const executionEvidence = buildFormalExecutionEvidence({
      runner: 'alloy',
      toolName: 'Alloy',
      toolVersion: '6.2.0',
      versionSource: 'cli',
      inputPaths: ['spec/alloy/Domain.als'],
      resultStatus: 'ok',
      exitCode: 0,
      logPath: 'artifacts/formal/alloy-output.txt',
      scope: 'Alloy fixture scope',
      assumptions: ['The fixture scope is bounded.'],
      executionOccurred: true,
    });
    expect(buildFormalRunnerOutput({ runner: 'alloy', executionEvidence })).toMatchObject({
      schemaVersion: 'formal-runner-output/v1',
      contractId: 'formal-runner-output.v1',
      artifactStatus: 'execution-report',
      producer: { id: 'ae.formal.verify-alloy' },
      executionEvidence: { provenance: 'runner-reported' },
    });
    expect(() => buildFormalRunnerOutput({ runner: 'tla', executionEvidence })).toThrow(
      'producer does not match the reviewed runner',
    );
  });

  it('rejects contradictory verified/unavailable provenance', () => {
    expect(hasEligibleToolVersion({
      version: '6.2.0',
      versionStatus: 'verified',
      versionSource: 'unavailable',
    })).toBe(false);
    expect(hasEligibleToolVersion({
      version: '6.2.0',
      versionStatus: 'verified',
      versionSource: 'cli',
    })).toBe(true);
  });
});
