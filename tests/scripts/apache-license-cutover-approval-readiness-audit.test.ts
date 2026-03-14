import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { execFileSync } from 'node:child_process';
import { afterEach, describe, expect, it } from 'vitest';
import {
  buildApacheLicenseCutoverApprovalReadinessAudit,
  parseApprovalRecord,
  renderMarkdownReport,
  run,
} from '../../scripts/legal/build-apache-license-cutover-approval-readiness.mjs';

const tempDirs = [];

function makeTempDir() {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'ae-cutover-approval-'));
  tempDirs.push(dir);
  return dir;
}

function initGitRepo(rootDir) {
  execFileSync('git', ['init'], { cwd: rootDir, stdio: 'ignore' });
  execFileSync('git', ['config', 'user.email', 'test@example.com'], { cwd: rootDir, stdio: 'ignore' });
  execFileSync('git', ['config', 'user.name', 'Test User'], { cwd: rootDir, stdio: 'ignore' });
  fs.writeFileSync(path.join(rootDir, '.gitkeep'), 'fixture\n');
  execFileSync('git', ['add', '.gitkeep'], { cwd: rootDir, stdio: 'ignore' });
  execFileSync('git', ['commit', '-m', 'test fixture'], { cwd: rootDir, stdio: 'ignore' });
  return execFileSync('git', ['rev-parse', 'HEAD'], { cwd: rootDir, encoding: 'utf8' }).trim();
}

afterEach(() => {
  for (const dir of tempDirs.splice(0)) {
    fs.rmSync(dir, { recursive: true, force: true });
  }
});

function buildApprovalRecordMarkdown({
  headSha = '1111111111111111111111111111111111111111',
  decisionRows = [
    ['Contributor / relicensing authority review', 'project owner + legal reviewer', 'approved', '2026-03-13', 'LEG-001'],
    ['Root `NOTICE` text approval', 'legal reviewer', 'approved', '2026-03-13', 'NOTICE-v3'],
    ['Trademark boundary review', 'brand / trademark owner', 'approved', '2026-03-13', 'TM-review'],
    ['Third-party notice review', 'legal reviewer', 'approved', '2026-03-13', 'No blockers'],
    ['Apache-2.0 cutover readiness audit review', 'project owner', 'approved', '2026-03-13', 'status=human-review-required; approvals recorded'],
  ],
  overallDecision = 'approved',
  approvedForCutover = 'yes',
  decisionDate = '2026-03-13',
  approvingOwner = 'owner@example.com',
  legalReviewer = 'legal@example.com',
} = {}) {
  return `---
# ignored front matter for parser
---

# Apache License Cutover Approval Record

## Audit Baseline

- head SHA: ${headSha}
- \`artifacts/reference/legal/license-scope-audit.json\`: artifacts/reference/legal/license-scope-audit.json
- \`artifacts/reference/legal/conditional-asset-audit.json\`: artifacts/reference/legal/conditional-asset-audit.json
- \`artifacts/reference/legal/notice-readiness-audit.json\`: artifacts/reference/legal/notice-readiness-audit.json
- \`artifacts/reference/legal/contributor-license-readiness-audit.json\`: artifacts/reference/legal/contributor-license-readiness-audit.json
- \`artifacts/reference/legal/third-party-notice-candidate-audit.json\`: artifacts/reference/legal/third-party-notice-candidate-audit.json
- \`artifacts/reference/legal/apache-license-cutover-readiness-audit.json\`: artifacts/reference/legal/apache-license-cutover-readiness-audit.json

## Required Approval Items

| Item | Required reviewer / owner | Decision | Date | Evidence / note |
| --- | --- | --- | --- | --- |
${decisionRows.map((row) => `| ${row.join(' | ')} |`).join('\n')}

## Decision Record

- overall decision: ${overallDecision}
- approved for cutover: ${approvedForCutover}
- decision date: ${decisionDate}
- approving owner: ${approvingOwner}
- legal reviewer: ${legalReviewer}
- notes: ready
`;
}

describe('apache license cutover approval readiness audit', () => {
  it('parses the approval record and builds a ready audit after human approvals close the loop', () => {
    const approvalRecord = parseApprovalRecord(buildApprovalRecordMarkdown());
    const audit = buildApacheLicenseCutoverApprovalReadinessAudit({
      approvalRecord,
      approvalRecordPath: 'docs/project/APACHE-LICENSE-CUTOVER-APPROVAL-RECORD.md',
      cutoverReadinessAudit: {
        gitHeadSha: '1111111111111111111111111111111111111111',
        readiness: { status: 'human-review-required' },
      },
      cutoverReadinessAuditPath: 'artifacts/reference/legal/apache-license-cutover-readiness-audit.json',
      gitHeadSha: '1111111111111111111111111111111111111111',
      generatedAt: '2026-03-13T00:00:00.000Z',
    });

    expect(audit.readiness.status).toBe('ready');
    expect(audit.summary.approvedCount).toBe(5);
    expect(audit.summary.pendingCount).toBe(0);
  });

  it('blocks when cutover readiness still has factual blockers', () => {
    const approvalRecord = parseApprovalRecord(buildApprovalRecordMarkdown());
    const audit = buildApacheLicenseCutoverApprovalReadinessAudit({
      approvalRecord,
      approvalRecordPath: 'docs/project/APACHE-LICENSE-CUTOVER-APPROVAL-RECORD.md',
      cutoverReadinessAudit: {
        gitHeadSha: '1111111111111111111111111111111111111111',
        readiness: { status: 'blocked' },
      },
      cutoverReadinessAuditPath: 'artifacts/reference/legal/apache-license-cutover-readiness-audit.json',
      gitHeadSha: '1111111111111111111111111111111111111111',
      generatedAt: '2026-03-13T00:00:00.000Z',
    });

    expect(audit.readiness.status).toBe('blocked');
    expect(audit.readiness.blockers.map((item) => item.code)).toContain('cutover-readiness-blocked');
  });

  it('returns human-review-required while approvals remain pending', () => {
    const approvalRecord = parseApprovalRecord(buildApprovalRecordMarkdown({
      decisionRows: [
        ['Contributor / relicensing authority review', 'project owner + legal reviewer', 'pending', '', ''],
        ['Root `NOTICE` text approval', 'legal reviewer', 'approved', '2026-03-13', 'NOTICE-v3'],
        ['Trademark boundary review', 'brand / trademark owner', 'approved', '2026-03-13', 'TM-review'],
        ['Third-party notice review', 'legal reviewer', 'approved', '2026-03-13', 'No blockers'],
        ['Apache-2.0 cutover readiness audit review', 'project owner', 'approved', '2026-03-13', 'status=ready'],
      ],
      overallDecision: 'pending',
      approvedForCutover: 'no',
      decisionDate: '',
      approvingOwner: '',
      legalReviewer: '',
    }));
    const audit = buildApacheLicenseCutoverApprovalReadinessAudit({
      approvalRecord,
      approvalRecordPath: 'docs/project/APACHE-LICENSE-CUTOVER-APPROVAL-RECORD.md',
      cutoverReadinessAudit: {
        gitHeadSha: '1111111111111111111111111111111111111111',
        readiness: { status: 'human-review-required' },
      },
      cutoverReadinessAuditPath: 'artifacts/reference/legal/apache-license-cutover-readiness-audit.json',
      gitHeadSha: '1111111111111111111111111111111111111111',
      generatedAt: '2026-03-13T00:00:00.000Z',
    });

    expect(audit.readiness.status).toBe('human-review-required');
    expect(audit.readiness.pendingItems).toContain('Contributor / relicensing authority review');
  });

  it('accepts the legacy approved for cutover PR key', () => {
    const approvalRecord = parseApprovalRecord(buildApprovalRecordMarkdown().replace(
      '- approved for cutover: yes',
      '- approved for cutover PR: yes',
    ));

    expect(approvalRecord.decisionRecord.approvedForCutover).toBe(true);
  });

  it('fails fast when an approval table row is malformed', () => {
    expect(() => parseApprovalRecord(buildApprovalRecordMarkdown({
      decisionRows: [
        ['Contributor / relicensing authority review', 'project owner + legal reviewer', 'approved', '2026-03-13', 'contains \\| pipe'],
      ],
    }).replace('contains \\| pipe', 'contains | pipe'))).toThrow('approval table row is malformed');
  });

  it('blocks when required approval items are missing from the table', () => {
    const approvalRecord = parseApprovalRecord(buildApprovalRecordMarkdown({
      decisionRows: [
        ['Contributor / relicensing authority review', 'project owner + legal reviewer', 'approved', '2026-03-13', 'LEG-001'],
      ],
    }));
    const audit = buildApacheLicenseCutoverApprovalReadinessAudit({
      approvalRecord,
      approvalRecordPath: 'docs/project/APACHE-LICENSE-CUTOVER-APPROVAL-RECORD.md',
      cutoverReadinessAudit: {
        gitHeadSha: '1111111111111111111111111111111111111111',
        readiness: { status: 'human-review-required' },
      },
      cutoverReadinessAuditPath: 'artifacts/reference/legal/apache-license-cutover-readiness-audit.json',
      gitHeadSha: '1111111111111111111111111111111111111111',
      generatedAt: '2026-03-13T00:00:00.000Z',
    });

    expect(audit.readiness.status).toBe('blocked');
    expect(audit.readiness.blockers.map((item) => item.code)).toContain('missing-required-approval-items');
    expect(audit.summary.requiredApprovalCount).toBe(5);
  });

  it('keeps blocked outputs schema-valid when audit paths are missing', () => {
    const markdown = buildApprovalRecordMarkdown().replace(
      '- `artifacts/reference/legal/conditional-asset-audit.json`: artifacts/reference/legal/conditional-asset-audit.json',
      '- `artifacts/reference/legal/conditional-asset-audit.json`:',
    );
    const approvalRecord = parseApprovalRecord(markdown);
    const audit = buildApacheLicenseCutoverApprovalReadinessAudit({
      approvalRecord,
      approvalRecordPath: 'docs/project/APACHE-LICENSE-CUTOVER-APPROVAL-RECORD.md',
      cutoverReadinessAudit: {
        gitHeadSha: '1111111111111111111111111111111111111111',
        readiness: { status: 'human-review-required' },
      },
      cutoverReadinessAuditPath: 'artifacts/reference/legal/apache-license-cutover-readiness-audit.json',
      gitHeadSha: '1111111111111111111111111111111111111111',
      generatedAt: '2026-03-13T00:00:00.000Z',
    });

    expect(audit.inputs.auditArtifactPaths.conditionalAssetAuditPath).toBeNull();
    expect(audit.readiness.status).toBe('blocked');
  });

  it('allows approval snapshot drift when the changed files stay within cutover scope', () => {
    const approvalRecord = parseApprovalRecord(buildApprovalRecordMarkdown({
      headSha: '2222222222222222222222222222222222222222',
    }));
    const audit = buildApacheLicenseCutoverApprovalReadinessAudit({
      approvalRecord,
      approvalRecordPath: 'docs/project/APACHE-LICENSE-CUTOVER-APPROVAL-RECORD.md',
      cutoverReadinessAudit: {
        gitHeadSha: '1111111111111111111111111111111111111111',
        readiness: { status: 'human-review-required' },
      },
      cutoverReadinessAuditPath: 'artifacts/reference/legal/apache-license-cutover-readiness-audit.json',
      gitHeadSha: '1111111111111111111111111111111111111111',
      changedFilesSinceApproval: [
        'LICENSE',
        'NOTICE',
        'package.json',
        'README.md',
        'CONTRIBUTING.md',
        'LICENSE-SCOPE.md',
        'TRADEMARKS.md',
        'THIRD_PARTY_NOTICES.md',
        'docs/project/APACHE-LICENSE-CUTOVER-APPROVAL-RECORD.md',
        'artifacts/reference/legal/apache-license-cutover-readiness-audit.json',
      ],
      generatedAt: '2026-03-13T00:00:00.000Z',
    });

    expect(audit.readiness.status).toBe('ready');
    expect(audit.inputs.approvalSnapshotMatchesCurrentHead).toBe(false);
    expect(audit.summary.unexpectedChangedFilesSinceApprovalCount).toBe(0);
  });

  it('blocks when approval snapshot drift includes non-cutover files', () => {
    const approvalRecord = parseApprovalRecord(buildApprovalRecordMarkdown({
      headSha: '2222222222222222222222222222222222222222',
    }));
    const audit = buildApacheLicenseCutoverApprovalReadinessAudit({
      approvalRecord,
      approvalRecordPath: 'docs/project/APACHE-LICENSE-CUTOVER-APPROVAL-RECORD.md',
      cutoverReadinessAudit: {
        gitHeadSha: '1111111111111111111111111111111111111111',
        readiness: { status: 'human-review-required' },
      },
      cutoverReadinessAuditPath: 'artifacts/reference/legal/apache-license-cutover-readiness-audit.json',
      gitHeadSha: '1111111111111111111111111111111111111111',
      changedFilesSinceApproval: [
        'LICENSE',
        'src/index.ts',
      ],
      generatedAt: '2026-03-13T00:00:00.000Z',
    });

    expect(audit.readiness.status).toBe('blocked');
    expect(audit.readiness.blockers.map((item) => item.code)).toContain('approval-snapshot-diverged-outside-cutover-scope');
    expect(audit.inputs.unexpectedChangedFilesSinceApproval).toEqual(['src/index.ts']);
  });

  it('renders a markdown report', () => {
    const approvalRecord = parseApprovalRecord(buildApprovalRecordMarkdown());
    const audit = buildApacheLicenseCutoverApprovalReadinessAudit({
      approvalRecord,
      approvalRecordPath: 'docs/project/APACHE-LICENSE-CUTOVER-APPROVAL-RECORD.md',
      cutoverReadinessAudit: {
        gitHeadSha: '1111111111111111111111111111111111111111',
        readiness: { status: 'human-review-required' },
      },
      cutoverReadinessAuditPath: 'artifacts/reference/legal/apache-license-cutover-readiness-audit.json',
      gitHeadSha: '1111111111111111111111111111111111111111',
      generatedAt: '2026-03-13T00:00:00.000Z',
    });

    const markdown = renderMarkdownReport(audit);
    expect(markdown).toContain('# Apache License Cutover Approval Readiness Audit');
    expect(markdown).toContain('- status: ready');
    expect(markdown).toContain('| Contributor / relicensing authority review |');
  });

  it('writes output files from the cli runner', () => {
    const rootDir = makeTempDir();
    const approvalRecordPath = path.join(rootDir, 'docs/project/APACHE-LICENSE-CUTOVER-APPROVAL-RECORD.md');
    const cutoverAuditPath = path.join(rootDir, 'artifacts/reference/legal/apache-license-cutover-readiness-audit.json');
    const outputJson = path.join(rootDir, 'artifacts/reference/legal/apache-license-cutover-approval-readiness-audit.json');
    const outputMd = path.join(rootDir, 'artifacts/reference/legal/apache-license-cutover-approval-readiness-audit.md');

    const gitHeadSha = initGitRepo(rootDir);
    fs.mkdirSync(path.dirname(approvalRecordPath), { recursive: true });
    fs.mkdirSync(path.dirname(cutoverAuditPath), { recursive: true });
    fs.writeFileSync(approvalRecordPath, buildApprovalRecordMarkdown({ headSha: gitHeadSha }));
    fs.writeFileSync(cutoverAuditPath, JSON.stringify({
      schemaVersion: 'apache-license-cutover-readiness-audit/v1',
      gitHeadSha,
      readiness: { status: 'human-review-required' },
    }, null, 2));

    const exitCode = run([
      'node',
      'scripts/legal/build-apache-license-cutover-approval-readiness.mjs',
      '--root',
      rootDir,
      '--approval-record',
      'docs/project/APACHE-LICENSE-CUTOVER-APPROVAL-RECORD.md',
      '--cutover-readiness-audit',
      'artifacts/reference/legal/apache-license-cutover-readiness-audit.json',
      '--output-json',
      'artifacts/reference/legal/apache-license-cutover-approval-readiness-audit.json',
      '--output-md',
      'artifacts/reference/legal/apache-license-cutover-approval-readiness-audit.md',
    ]);

    expect(exitCode).toBe(0);
    expect(JSON.parse(fs.readFileSync(outputJson, 'utf8')).schemaVersion).toBe('apache-license-cutover-approval-readiness-audit/v1');
    expect(fs.readFileSync(outputMd, 'utf8')).toContain('Apache License Cutover Approval Readiness Audit');
  });
});
