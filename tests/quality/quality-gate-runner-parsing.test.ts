import { describe, expect, it } from 'vitest';
import { QualityGateRunner } from '../../src/quality/quality-gate-runner.js';
import type { QualityGateResult } from '../../src/quality/policy-loader.js';

type ParseLintingResult = (
  baseResult: QualityGateResult,
  result: { stdout: string; stderr?: string; code?: number },
  threshold: { maxErrors?: number; maxWarnings?: number },
) => QualityGateResult;

type ParseSecurityResult = (
  baseResult: QualityGateResult,
  result: { stdout: string; stderr?: string; code?: number },
  threshold: { maxCritical?: number; maxHigh?: number; maxMedium?: number },
) => QualityGateResult;

const createBaseResult = (gateKey: string, gateName: string): QualityGateResult => ({
  gateKey,
  gateName,
  passed: false,
  violations: [],
  executionTime: 0,
  environment: 'testing',
  threshold: {},
});

describe('QualityGateRunner result parsing', () => {
  it('treats lint gate as pass when counts are within threshold even with non-zero exit', () => {
    const runner = new QualityGateRunner();
    const parseLintingResult = (runner as unknown as { parseLintingResult: ParseLintingResult }).parseLintingResult;
    const result = parseLintingResult(
      createBaseResult('linting', 'Code Linting'),
      {
        stdout: '0 error lint-delta (actual 2285, baseline 2365)\n8 warning rule-delta above baseline\n',
        code: 1,
      },
      { maxErrors: 5, maxWarnings: 20 },
    );

    expect(result.passed).toBe(true);
    expect(result.violations).toHaveLength(0);
    expect(result.details).toEqual({ errors: 0, warnings: 8 });
  });

  it('fails lint gate on non-zero exit when counts cannot be parsed', () => {
    const runner = new QualityGateRunner();
    const parseLintingResult = (runner as unknown as { parseLintingResult: ParseLintingResult }).parseLintingResult;
    const result = parseLintingResult(
      createBaseResult('linting', 'Code Linting'),
      { stdout: '', stderr: 'eslint crashed', code: 2 },
      { maxErrors: 5, maxWarnings: 20 },
    );

    expect(result.passed).toBe(false);
    expect(result.violations).toContain('Linting command failed with exit code 2');
  });

  it('parses security counts from JSON output and applies thresholds', () => {
    const runner = new QualityGateRunner();
    const parseSecurityResult = (runner as unknown as { parseSecurityResult: ParseSecurityResult }).parseSecurityResult;
    const result = parseSecurityResult(
      createBaseResult('security', 'Security Vulnerabilities'),
      {
        stdout: JSON.stringify({
          metadata: {
            vulnerabilities: { critical: 0, high: 6, moderate: 5, low: 2, info: 0 },
          },
        }),
        code: 1,
      },
      { maxCritical: 2, maxHigh: 6, maxMedium: 15 },
    );

    expect(result.passed).toBe(true);
    expect(result.violations).toHaveLength(0);
    expect(result.details).toEqual({ critical: 0, high: 6, medium: 5 });
  });

  it('fails security gate when vulnerabilities exceed thresholds', () => {
    const runner = new QualityGateRunner();
    const parseSecurityResult = (runner as unknown as { parseSecurityResult: ParseSecurityResult }).parseSecurityResult;
    const result = parseSecurityResult(
      createBaseResult('security', 'Security Vulnerabilities'),
      {
        stdout: JSON.stringify({
          metadata: {
            vulnerabilities: { critical: 0, high: 7, moderate: 2, low: 1, info: 0 },
          },
        }),
        code: 1,
      },
      { maxCritical: 2, maxHigh: 6, maxMedium: 15 },
    );

    expect(result.passed).toBe(false);
    expect(result.violations).toContain('Too many high vulnerabilities: 7 > 6');
  });
});
