import { describe, expect, it } from 'vitest';
import { mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join, resolve } from 'node:path';
import { tmpdir } from 'node:os';

const repoRoot = resolve('.');
const scriptPath = resolve(repoRoot, 'scripts/summary/render-pr-summary.mjs');

const runScript = (cwd: string, env: Record<string, string>) =>
  spawnSync('node', [scriptPath], {
    cwd,
    encoding: 'utf8',
    timeout: 120_000,
    env: {
      ...process.env,
      ...env,
    },
  });

describe.sequential('render-pr-summary', () => {
  it('renders assurance digest when assurance summary exists', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-render-pr-summary-digest-'));

    try {
      mkdirSync(join(sandbox, 'artifacts', 'summary'), { recursive: true });
      mkdirSync(join(sandbox, 'artifacts', 'assurance'), { recursive: true });

      writeFileSync(
        join(sandbox, 'artifacts', 'summary', 'combined.json'),
        JSON.stringify(
          {
            adapters: [{ adapter: 'playwright', summary: '12/12 passed', status: 'ok', traceId: 'trace-1' }],
            formal: { result: 'pass', traceId: 'trace-2' },
            replay: { totalEvents: 4, violatedInvariants: [], traceId: 'trace-3' },
          },
          null,
          2,
        ),
      );

      writeFileSync(
        join(sandbox, 'artifacts', 'assurance', 'assurance-summary.json'),
        JSON.stringify(
          {
            summary: {
              claimCount: 2,
              satisfiedClaims: 1,
              warningClaims: 1,
              warningCount: 2,
            },
            warnings: [
              { code: 'missing-spec-derived-evidence' },
              { code: 'insufficient-independent-lanes' },
            ],
            laneCoverage: {
              spec: { requiredClaims: 2, observedClaims: 1 },
              behavior: { requiredClaims: 1, observedClaims: 1 },
              adversarial: { requiredClaims: 1, observedClaims: 0 },
              model: { requiredClaims: 1, observedClaims: 1 },
              proof: { requiredClaims: 0, observedClaims: 0 },
              runtime: { requiredClaims: 0, observedClaims: 0 },
            },
          },
          null,
          2,
        ),
      );

      const result = runScript(sandbox, { SUMMARY_MODE: 'digest', SUMMARY_LANG: 'en' });
      expect(result.status, result.stderr || result.stdout).toBe(0);

      const output = readFileSync(join(sandbox, 'artifacts', 'summary', 'PR_SUMMARY.md'), 'utf8');
      expect(output).toContain('Assurance: satisfied=1/2, warningClaims=1, warnings=2');
      expect(output).toContain('Assurance warning codes: missing-spec-derived-evidence, insufficient-independent-lanes');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('renders quality scorecard when the artifact exists', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-render-pr-summary-scorecard-'));

    try {
      mkdirSync(join(sandbox, 'artifacts', 'summary'), { recursive: true });
      mkdirSync(join(sandbox, 'artifacts', 'quality'), { recursive: true });

      writeFileSync(
        join(sandbox, 'artifacts', 'summary', 'combined.json'),
        JSON.stringify(
          {
            adapters: [{ adapter: 'playwright', summary: '12/12 passed', status: 'ok' }],
            formal: { result: 'pass' },
            replay: { totalEvents: 2, violatedInvariants: [] },
          },
          null,
          2,
        ),
      );

      writeFileSync(
        join(sandbox, 'artifacts', 'quality', 'quality-scorecard.json'),
        JSON.stringify(
          {
            summary: {
              overallStatus: 'warn',
              overallScore: 78,
            },
            blockers: [
              { dimension: 'policyReadiness', code: 'policy-gate-warning' },
            ],
          },
          null,
          2,
        ),
      );

      const result = runScript(sandbox, { SUMMARY_MODE: 'digest', SUMMARY_LANG: 'en' });
      expect(result.status, result.stderr || result.stdout).toBe(0);

      const output = readFileSync(join(sandbox, 'artifacts', 'summary', 'PR_SUMMARY.md'), 'utf8');
      expect(output).toContain('Quality Scorecard: warn 78/100');
      expect(output).toContain('Quality blockers: policyReadiness:policy-gate-warning');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('renders assurance section in detailed Japanese mode', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-render-pr-summary-detailed-'));

    try {
      mkdirSync(join(sandbox, 'artifacts', 'summary'), { recursive: true });
      mkdirSync(join(sandbox, 'artifacts', 'assurance'), { recursive: true });

      writeFileSync(
        join(sandbox, 'artifacts', 'summary', 'combined.json'),
        JSON.stringify(
          {
            adapters: [{ adapter: 'playwright', summary: '12/12 passed', status: 'ok' }],
            formal: { result: 'pass' },
          },
          null,
          2,
        ),
      );

      writeFileSync(
        join(sandbox, 'artifacts', 'assurance', 'assurance-summary.json'),
        JSON.stringify(
          {
            summary: {
              claimCount: 1,
              satisfiedClaims: 1,
              warningClaims: 0,
              warningCount: 0,
            },
            warnings: [],
            laneCoverage: {
              spec: { requiredClaims: 1, observedClaims: 1 },
              behavior: { requiredClaims: 1, observedClaims: 1 },
              adversarial: { requiredClaims: 0, observedClaims: 0 },
              model: { requiredClaims: 1, observedClaims: 1 },
              proof: { requiredClaims: 0, observedClaims: 0 },
              runtime: { requiredClaims: 0, observedClaims: 0 },
            },
          },
          null,
          2,
        ),
      );

      const result = runScript(sandbox, { SUMMARY_MODE: 'detailed', SUMMARY_LANG: 'ja' });
      expect(result.status, result.stderr || result.stdout).toBe(0);

      const output = readFileSync(join(sandbox, 'artifacts', 'summary', 'PR_SUMMARY.md'), 'utf8');
      expect(output).toContain('## 品質サマリ');
      expect(output).toContain('- 保証: 適合=1/1, 警告claim=0, 警告=0');
      expect(output).toContain('- 保証レーン: spec 1/1, behavior 1/1, adversarial 0/0, model 1/1, proof 0/0, runtime 0/0');
      expect(output).toContain('- 保証 warning code: なし');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('omits assurance placeholders when the assurance artifact is missing', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-render-pr-summary-no-assurance-'));

    try {
      mkdirSync(join(sandbox, 'artifacts', 'summary'), { recursive: true });

      writeFileSync(
        join(sandbox, 'artifacts', 'summary', 'combined.json'),
        JSON.stringify(
          {
            adapters: [{ adapter: 'playwright', summary: '12/12 passed', status: 'ok' }],
            formal: { result: 'pass' },
            replay: { totalEvents: 2, violatedInvariants: [] },
          },
          null,
          2,
        ),
      );

      const result = runScript(sandbox, { SUMMARY_MODE: 'digest', SUMMARY_LANG: 'en' });
      expect(result.status, result.stderr || result.stdout).toBe(0);

      const output = readFileSync(join(sandbox, 'artifacts', 'summary', 'PR_SUMMARY.md'), 'utf8');
      expect(output).not.toContain('Assurance: n/a');
      expect(output).not.toContain('Assurance warning codes');
      expect(output).not.toContain('保証: なし');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });
});
