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

  it('renders claim evidence manifest when the artifact exists', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-render-pr-summary-claim-evidence-'));

    try {
      mkdirSync(join(sandbox, 'artifacts', 'summary'), { recursive: true });
      mkdirSync(join(sandbox, 'artifacts', 'assurance'), { recursive: true });

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
        join(sandbox, 'artifacts', 'assurance', 'claim-evidence-manifest.json'),
        JSON.stringify(
          {
            summary: {
              totalClaims: 3,
              fullySupported: 1,
              partiallySupported: 1,
              waived: 1,
              unresolved: 0,
              security: {
                claims: 1,
                findings: 3,
                reviews: 3,
                candidate: 0,
                needsHumanReview: 1,
                confirmed: 0,
                rejected: 1,
                waived: 0,
                outOfScope: 1,
                highOrCriticalOpen: 1,
              },
            },
            claims: [
              { id: 'satisfied-claim', missingEvidenceRefs: [], waiverRefs: [] },
              { id: 'partial-claim', missingEvidenceRefs: [{ id: 'missing-runtime' }], waiverRefs: [] },
              { id: 'waived-claim', missingEvidenceRefs: [], waiverRefs: [{ id: 'waiver-001' }] },
            ],
          },
          null,
          2,
        ),
      );

      const result = runScript(sandbox, { SUMMARY_MODE: 'digest', SUMMARY_LANG: 'en' });
      expect(result.status, result.stderr || result.stdout).toBe(0);

      const output = readFileSync(join(sandbox, 'artifacts', 'summary', 'PR_SUMMARY.md'), 'utf8');
      expect(output).toContain('Claim evidence: satisfied=1/3, partial=1, waived=1, unresolved=0');
      expect(output).toContain('Claim evidence refs: missing=1, waivers=1');
      expect(output).toContain('Security findings: total=3, needs-human-review=1, high/critical-open=1');
      expect(output).toContain('assumption-validation-required=n/a, assumption-residual-risk=n/a');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('renders change-package v2 claims, proof obligations, and waivers when the artifact exists', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-render-pr-summary-change-package-v2-'));

    try {
      mkdirSync(join(sandbox, 'artifacts', 'summary'), { recursive: true });
      mkdirSync(join(sandbox, 'artifacts', 'change-package'), { recursive: true });

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
        join(sandbox, 'artifacts', 'change-package', 'change-package-v2.json'),
        JSON.stringify(
          {
            schemaVersion: 'change-package/v2',
            assurance: {
              targetLevel: 'A3',
              achievedLevel: 'A2',
              status: 'partial',
            },
            claims: [
              { id: 'no-negative-stock', status: 'tested' },
              { id: 'manual-review', status: 'waived' },
              { id: 'strict-proof', status: 'failed' },
              { id: 'ui-out-of-scope', status: 'not-applicable' },
            ],
            proofObligations: [
              { id: 'obl-no-negative-stock' },
            ],
            waivers: [
              { owner: '@team-risk', relatedClaimIds: ['manual-review'] },
            ],
            policyDecision: {
              result: 'report-only',
              mode: 'report-only',
              enforced: false,
            },
            releaseControls: {
              preDeployChecks: ['pnpm run verify:lite'],
              postDeployChecks: ['post-deploy-verify'],
              rollbackSignals: ['post-deploy-verify.status=fail'],
            },
          },
          null,
          2,
        ),
      );

      const result = runScript(sandbox, { SUMMARY_MODE: 'digest', SUMMARY_LANG: 'en' });
      expect(result.status, result.stderr || result.stdout).toBe(0);

      const output = readFileSync(join(sandbox, 'artifacts', 'summary', 'PR_SUMMARY.md'), 'utf8');
      expect(output).toContain('Change Package v2: claims=4, proofObligations=1, waivers=1, assurance=A3/A2/partial');
      expect(output).toContain('evidencePackage=artifacts/change-package/change-package-v2.json');
      expect(output).toContain('claimStates=satisfied=0, tested=1, model-checked=0, proved=0, runtime-mitigated=0, waived=1, unresolved=0, failed=1, not-applicable=1');
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

  it('renders discovery pack rollout details when verify-lite summary exists', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-render-pr-summary-discovery-'));

    try {
      mkdirSync(join(sandbox, 'artifacts', 'summary'), { recursive: true });
      mkdirSync(join(sandbox, 'artifacts', 'verify-lite'), { recursive: true });

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
        join(sandbox, 'artifacts', 'verify-lite', 'verify-lite-run-summary.json'),
        JSON.stringify(
          {
            discoveryPack: {
              mode: 'strict',
              reason: 'label:enforce-discovery',
              sourcePresent: true,
              strictApproved: true,
              failOn: [
                'blocking-open-questions',
                'orphan-approved-requirements',
                'orphan-approved-business-use-cases',
              ],
              validateStatus: 'warn',
              compileStatus: 'pass',
              scannedFiles: 3,
              warningFiles: 1,
              failedFiles: 0,
              blockingOpenQuestions: 1,
              orphanApprovedRequirements: 2,
              orphanApprovedBusinessUseCases: 0,
              compileSelectedCount: 8,
              compileExcludedByStatusCount: 2,
              compileSkippedByTargetCount: 0,
            },
          },
          null,
          2,
        ),
      );

      const result = runScript(sandbox, { SUMMARY_MODE: 'digest', SUMMARY_LANG: 'en' });
      expect(result.status, result.stderr || result.stdout).toBe(0);

      const output = readFileSync(join(sandbox, 'artifacts', 'summary', 'PR_SUMMARY.md'), 'utf8');
      expect(output).toContain(
        'Discovery Pack: strict warn (blockingOpenQuestions=1, orphanRequirements=2, orphanBusinessUseCases=0, reason=label:enforce-discovery)',
      );
      expect(output).toContain('Discovery compile: pass (selected=8, excluded=2, skippedByTarget=0)');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('prefers canonical formal-summary v2 over the legacy formal summary fallback', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-render-pr-summary-formal-v2-'));

    try {
      mkdirSync(join(sandbox, 'artifacts', 'summary'), { recursive: true });
      mkdirSync(join(sandbox, 'artifacts', 'formal'), { recursive: true });
      mkdirSync(join(sandbox, 'formal'), { recursive: true });

      writeFileSync(
        join(sandbox, 'artifacts', 'summary', 'combined.json'),
        JSON.stringify(
          {
            adapters: [{ adapter: 'playwright', summary: '12/12 passed', status: 'ok' }],
          },
          null,
          2,
        ),
      );
      writeFileSync(
        join(sandbox, 'artifacts', 'formal', 'formal-summary-v2.json'),
        JSON.stringify(
          {
            schemaVersion: 'formal-summary/v2',
            contractId: 'formal-summary.v2',
            tool: 'aggregate',
            status: 'ok',
            ok: true,
            generatedAtUtc: '2026-03-04T00:00:00.000Z',
            metadata: {},
            results: [],
          },
          null,
          2,
        ),
      );
      writeFileSync(
        join(sandbox, 'formal', 'summary.json'),
        JSON.stringify({ result: 'fail', traceId: 'legacy-trace' }, null, 2),
      );

      const result = runScript(sandbox, { SUMMARY_MODE: 'digest', SUMMARY_LANG: 'en' });
      expect(result.status, result.stderr || result.stdout).toBe(0);

      const output = readFileSync(join(sandbox, 'artifacts', 'summary', 'PR_SUMMARY.md'), 'utf8');
      expect(output).toContain('Formal: pass');
      expect(output).not.toContain('Formal: fail');
      expect(output).not.toContain('legacy-trace');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('uses the hermetic formal aggregate before the legacy formal summary fallback', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-render-pr-summary-formal-hermetic-'));

    try {
      mkdirSync(join(sandbox, 'artifacts', 'summary'), { recursive: true });
      mkdirSync(join(sandbox, 'artifacts', 'hermetic-reports', 'formal'), { recursive: true });
      mkdirSync(join(sandbox, 'formal'), { recursive: true });

      writeFileSync(
        join(sandbox, 'artifacts', 'summary', 'combined.json'),
        JSON.stringify(
          {
            adapters: [{ adapter: 'playwright', summary: '12/12 passed', status: 'ok' }],
          },
          null,
          2,
        ),
      );
      writeFileSync(
        join(sandbox, 'artifacts', 'hermetic-reports', 'formal', 'summary.json'),
        JSON.stringify(
          {
            present: {
              conformance: true,
              smt: false,
              alloy: false,
            },
          },
          null,
          2,
        ),
      );
      writeFileSync(
        join(sandbox, 'formal', 'summary.json'),
        JSON.stringify({ result: 'fail' }, null, 2),
      );

      const result = runScript(sandbox, { SUMMARY_MODE: 'digest', SUMMARY_LANG: 'en' });
      expect(result.status, result.stderr || result.stdout).toBe(0);

      const output = readFileSync(join(sandbox, 'artifacts', 'summary', 'PR_SUMMARY.md'), 'utf8');
      expect(output).toContain('Formal: present 1/3 (conformance)');
      expect(output).not.toContain('Formal: fail');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('reads downloaded verify-lite formal summaries before the legacy formal summary fallback', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-render-pr-summary-formal-downloaded-'));

    try {
      mkdirSync(join(sandbox, 'artifacts', 'summary'), { recursive: true });
      mkdirSync(join(sandbox, 'artifacts', 'downloaded', 'verify-lite-report', 'artifacts', 'formal'), { recursive: true });
      mkdirSync(join(sandbox, 'formal'), { recursive: true });

      writeFileSync(
        join(sandbox, 'artifacts', 'summary', 'combined.json'),
        JSON.stringify(
          {
            adapters: [{ adapter: 'playwright', summary: '12/12 passed', status: 'ok' }],
          },
          null,
          2,
        ),
      );
      writeFileSync(
        join(sandbox, 'artifacts', 'downloaded', 'verify-lite-report', 'artifacts', 'formal', 'formal-summary-v2.json'),
        JSON.stringify(
          {
            schemaVersion: 'formal-summary/v2',
            contractId: 'formal-summary.v2',
            tool: 'aggregate',
            status: 'ok',
            ok: true,
            generatedAtUtc: '2026-03-04T00:00:00.000Z',
            metadata: {},
            results: [],
          },
          null,
          2,
        ),
      );
      writeFileSync(
        join(sandbox, 'formal', 'summary.json'),
        JSON.stringify({ result: 'fail' }, null, 2),
      );

      const result = runScript(sandbox, { SUMMARY_MODE: 'digest', SUMMARY_LANG: 'en' });
      expect(result.status, result.stderr || result.stdout).toBe(0);

      const output = readFileSync(join(sandbox, 'artifacts', 'summary', 'PR_SUMMARY.md'), 'utf8');
      expect(output).toContain('Formal: pass');
      expect(output).not.toContain('Formal: fail');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('keeps the legacy formal summary as the final compatibility fallback', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-render-pr-summary-formal-legacy-'));

    try {
      mkdirSync(join(sandbox, 'artifacts', 'summary'), { recursive: true });
      mkdirSync(join(sandbox, 'formal'), { recursive: true });

      writeFileSync(
        join(sandbox, 'artifacts', 'summary', 'combined.json'),
        JSON.stringify(
          {
            adapters: [{ adapter: 'playwright', summary: '12/12 passed', status: 'ok' }],
          },
          null,
          2,
        ),
      );
      writeFileSync(
        join(sandbox, 'formal', 'summary.json'),
        JSON.stringify({ result: 'fail', traceId: 'legacy-trace' }, null, 2),
      );

      const result = runScript(sandbox, { SUMMARY_MODE: 'digest', SUMMARY_LANG: 'en' });
      expect(result.status, result.stderr || result.stdout).toBe(0);

      const output = readFileSync(join(sandbox, 'artifacts', 'summary', 'PR_SUMMARY.md'), 'utf8');
      expect(output).toContain('Formal: fail');
      expect(output).toContain('Trace: legacy-trace');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('keeps the workflow inline fallback formal order aligned with canonical routes', () => {
    const workflow = readFileSync(resolve(repoRoot, '.github/workflows/pr-ci-status-comment.yml'), 'utf8');
    const resolveRunStep = workflow.indexOf('name: Resolve verify-lite run for current head SHA');
    const downloadStep = workflow.indexOf('name: Download verify-lite report artifact');
    const renderStep = workflow.indexOf('name: Generate Markdown summary');
    expect(resolveRunStep).toBeGreaterThanOrEqual(0);
    expect(downloadStep).toBeGreaterThan(resolveRunStep);
    expect(renderStep).toBeGreaterThan(downloadStep);

    const selectorStart = workflow.indexOf('function selectFormalSummary(c)');
    expect(selectorStart).toBeGreaterThanOrEqual(0);

    const selector = workflow.slice(selectorStart, workflow.indexOf('const c = r("artifacts/summary/combined.json")', selectorStart));
    const combinedIndex = selector.indexOf('c.formal');
    const v2Index = selector.indexOf('artifacts/formal/formal-summary-v2.json');
    const downloadedV2Index = selector.indexOf('artifacts/downloaded/verify-lite-report/artifacts/formal/formal-summary-v2.json');
    const v1Index = selector.indexOf('artifacts/formal/formal-summary-v1.json');
    const downloadedV1Index = selector.indexOf('artifacts/downloaded/verify-lite-report/artifacts/formal/formal-summary-v1.json');
    const hermeticIndex = selector.indexOf('artifacts/hermetic-reports/formal/summary.json');
    const downloadedHermeticIndex = selector.indexOf('artifacts/downloaded/verify-lite-report/artifacts/hermetic-reports/formal/summary.json');
    const legacyIndex = selector.indexOf('r("formal/summary.json")');

    expect([
      combinedIndex,
      v2Index,
      downloadedV2Index,
      v1Index,
      downloadedV1Index,
      hermeticIndex,
      downloadedHermeticIndex,
      legacyIndex,
    ].every((index) => index >= 0)).toBe(true);
    expect(combinedIndex).toBeLessThan(v2Index);
    expect(v2Index).toBeLessThan(downloadedV2Index);
    expect(downloadedV2Index).toBeLessThan(v1Index);
    expect(v1Index).toBeLessThan(downloadedV1Index);
    expect(downloadedV1Index).toBeLessThan(hermeticIndex);
    expect(hermeticIndex).toBeLessThan(downloadedHermeticIndex);
    expect(downloadedHermeticIndex).toBeLessThan(legacyIndex);
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
