import fs from 'node:fs';
import path from 'node:path';
import { afterEach, describe, expect, it } from 'vitest';
import {
  EVIDENCE_DEFINITIONS,
  buildChecklist,
  buildPostureReport,
  evidenceFromFixture,
  missingLiveEvidence,
  parseArgs,
  renderMarkdown,
} from '../../../scripts/security/collect-live-posture.mjs';

const tmpDirs: string[] = [];

const makeTmpDir = () => {
  const base = path.join(process.cwd(), 'artifacts', 'tmp', 'unit-tests');
  fs.mkdirSync(base, { recursive: true });
  const dir = fs.mkdtempSync(path.join(base, 'live-posture-'));
  tmpDirs.push(dir);
  return dir;
};

afterEach(() => {
  for (const dir of tmpDirs.splice(0)) {
    fs.rmSync(dir, { recursive: true, force: true });
  }
});

describe('live operational posture collector', () => {
  it('builds a checklist from collected branch, workflow, secrets, variables, runner, and egress evidence', () => {
    const evidence = evidenceFromFixture({
      repository: { default_branch: 'main', visibility: 'public' },
      branchProtection: {
        required_status_checks: { checks: [{ context: 'verify-lite' }, { context: 'policy-gate' }] },
        required_pull_request_reviews: { required_approving_review_count: 1 },
      },
      rulesets: { total_count: 1, rulesets: [{ name: 'main' }] },
      actionsPermissions: { enabled: true, allowed_actions: 'selected' },
      workflowPermissions: { default_workflow_permissions: 'read', can_approve_pull_request_reviews: false },
      forkPrApproval: { approval_policy: 'first_time_contributors' },
      secrets: { total_count: 3 },
      variables: { total_count: 4 },
      selfHostedRunners: { total_count: 0, runners: [] },
      workflows: { total_count: 18 },
      runnerEgress: { policy: 'restricted via corporate proxy', reviewedAt: '2026-06-07' },
    });

    const checklist = buildChecklist(evidence);
    const byId = new Map(checklist.map((item) => [item.id, item]));

    expect(byId.get('branch-ruleset-protection')?.status).toBe('satisfied');
    expect(byId.get('workflow-token-permissions')?.status).toBe('satisfied');
    expect(byId.get('actions-approval-policy')?.status).toBe('satisfied');
    expect(byId.get('secrets-variables-inventory')?.status).toBe('satisfied');
    expect(byId.get('runner-inventory')?.status).toBe('satisfied');
    expect(byId.get('runner-egress-policy')?.status).toBe('needs-review');
    expect(byId.get('live-evidence-gap-disclosure')?.status).toBe('satisfied');
  });

  it('keeps no-live collection explicit as missing evidence residual risk', () => {
    const evidence = missingLiveEvidence('live collection disabled in test');
    const report = buildPostureReport({
      repository: 'itdojp/ae-framework',
      evidence,
      generatedAt: '2026-06-07T00:00:00.000Z',
      evidenceMode: 'not-collected',
    });

    expect(report.summary.missingEvidence).toBeGreaterThan(0);
    expect(report.summary.missingEvidenceIds).toContain('branchProtection');
    expect(report.checklist.find((item) => item.id === 'live-evidence-gap-disclosure')?.status).toBe('missing-evidence');

    const markdown = renderMarkdown(report);
    expect(markdown).toContain('Live evidence not collected for:');
    expect(markdown).toContain('branchProtection');
    expect(markdown).toContain('Runner egress policy evidence');
    expect(markdown).toContain('live collection disabled in test');
  });

  it('preserves missing evidence when replaying a generated report as a fixture', () => {
    const original = buildPostureReport({
      repository: 'itdojp/ae-framework',
      evidence: missingLiveEvidence('first pass missing live evidence'),
      generatedAt: '2026-06-07T00:00:00.000Z',
      evidenceMode: 'not-collected',
    });

    const replayEvidence = evidenceFromFixture(original.evidence);
    const replayed = buildPostureReport({
      repository: 'itdojp/ae-framework',
      evidence: replayEvidence,
      generatedAt: '2026-06-07T00:00:00.000Z',
      evidenceMode: 'fixture',
    });

    expect(replayEvidence.branchProtection.status).toBe('missing');
    expect(replayed.summary.missingEvidenceIds).toContain('branchProtection');
    expect(replayed.checklist.find((item) => item.id === 'live-evidence-gap-disclosure')?.status).toBe('missing-evidence');
  });

  it('renders deterministic markdown and JSON-compatible report summaries', () => {
    const evidence = evidenceFromFixture({
      repository: { default_branch: 'main', visibility: 'private' },
      workflows: { total_count: 7 },
    });
    const report = buildPostureReport({
      repository: 'itdojp/ae-framework',
      evidence,
      generatedAt: '2026-06-07T00:00:00.000Z',
      evidenceMode: 'fixture',
    });
    const markdown = renderMarkdown(report);

    expect(report.schemaVersion).toBe('live-operational-posture/v1');
    expect(report.summary.totalControls).toBe(report.checklist.length);
    expect(markdown).toContain('| Control | Category | Status | Evidence | Operator action |');
    expect(markdown).toContain('workflowCount=7');
    expect(JSON.parse(JSON.stringify(report)).repository).toBe('itdojp/ae-framework');
  });

  it('parses CLI options and writes under caller-provided output paths', () => {
    const dir = makeTmpDir();
    const options = parseArgs([
      '--',
      '--repo',
      'itdojp/ae-framework',
      '--no-live',
      '--output-json',
      path.join(dir, 'posture.json'),
      '--output-md',
      path.join(dir, 'posture.md'),
      '--generated-at',
      '2026-06-07T00:00:00.000Z',
    ]);

    expect(options.repo).toBe('itdojp/ae-framework');
    expect(options.noLive).toBe(true);
    expect(options.outputJson).toContain('posture.json');
    expect(options.outputMd).toContain('posture.md');
    expect(options.generatedAt).toBe('2026-06-07T00:00:00.000Z');
  });

  it('URL-encodes default branch names in branch protection endpoints', () => {
    const branchProtection = EVIDENCE_DEFINITIONS.find((definition) => definition.id === 'branchProtection');

    expect(branchProtection?.endpoint?.('itdojp/ae-framework', { defaultBranch: 'release/2026.06' })).toBe(
      'repos/itdojp/ae-framework/branches/release%2F2026.06/protection',
    );
  });
});
