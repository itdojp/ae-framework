import { describe, expect, it } from 'vitest';
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join, resolve } from 'node:path';
import { tmpdir } from 'node:os';
import { pathToFileURL } from 'node:url';

const repoRoot = resolve('.');
const scriptPath = resolve(repoRoot, 'scripts/maintenance/remote-cleanup-ambiguous-evidence.mjs');
const moduleUrl = pathToFileURL(scriptPath).href;

const createBatchPayload = () => ({
  generatedAt: '2026-03-08T00:00:00Z',
  batch: {
    id: 'C',
    title: 'Ambiguous stale branches',
    description: 'manual review',
    criteria: 'remoteStale[*] where prState == ambiguous',
  },
  sourceTriage: {
    path: '/tmp/remote-branch-triage.json',
    generatedAt: '2026-03-08T00:00:00Z',
    inventoryGeneratedAt: '2026-03-07T23:50:00Z',
    base: 'origin/main',
    remote: 'origin',
  },
  count: 2,
  items: [
    {
      branch: 'feature/ambiguous-a',
      ageDays: 200,
      branchOid: 'oid-a',
      riskBand: 'high',
      prState: 'ambiguous',
      prMatchMode: 'branch-name-only',
      latestPr: { number: 2401, state: 'merged' },
      proposedAction: 'manual-review',
      decision: '',
      notes: '',
      baseBranches: ['main'],
    },
    {
      branch: 'docs/ambiguous-b',
      ageDays: 150,
      branchOid: 'oid-b',
      riskBand: 'low',
      prState: 'ambiguous',
      prMatchMode: 'branch-name-only',
      latestPr: { number: 2402, state: 'closed' },
      proposedAction: 'manual-review',
      decision: '',
      notes: '',
      baseBranches: [],
    },
  ],
});

const createAuditPayload = () => ({
  generatedAt: '2026-03-08T00:10:00Z',
  batch: {
    id: 'C',
    title: 'Ambiguous stale branches',
    description: 'manual review',
    criteria: 'remoteStale[*] where prState == ambiguous',
  },
  sourceTriage: {
    path: '/tmp/remote-branch-triage.json',
    generatedAt: '2026-03-08T00:00:00Z',
    inventoryGeneratedAt: '2026-03-07T23:50:00Z',
    base: 'origin/main',
    remote: 'origin',
  },
  summary: {
    total: 2,
    withOpenIssueRefs: 1,
    withAutomationRefs: 1,
    withPlanRefs: 0,
    withCodeRefs: 0,
    clearCandidates: 1,
  },
  items: [
    {
      branch: 'feature/ambiguous-a',
      ageDays: 200,
      branchOid: 'oid-a',
      prState: 'ambiguous',
      prMatchMode: 'branch-name-only',
      latestPr: { number: 2401, state: 'merged' },
      audit: {
        reviewHint: 'keep-review',
        openIssueRefs: [{ number: 2469, source: 'body', url: 'https://example.invalid/issues/2469' }],
        repoRefs: [{ path: '.github/workflows/cleanup.yml', category: 'automation', lineMatches: [{ line: 12, text: 'feature/ambiguous-a' }] }],
        repoRefSummary: { automation: 1, plan: 0, code: 0, history: 0 },
      },
    },
    {
      branch: 'docs/ambiguous-b',
      ageDays: 150,
      branchOid: 'oid-b',
      prState: 'ambiguous',
      prMatchMode: 'branch-name-only',
      latestPr: { number: 2402, state: 'closed' },
      audit: {
        reviewHint: 'manual-review',
        openIssueRefs: [],
        repoRefs: [],
        repoRefSummary: { automation: 0, plan: 0, code: 0, history: 0 },
      },
    },
  ],
});

describe.sequential('remote-cleanup-ambiguous-evidence script', () => {
  it('renders a consolidated Batch C evidence bundle', async () => {
    const mod = await import(moduleUrl);
    expect(mod.parseArgs([])).toMatchObject({
      batchJson: 'tmp/maintenance/remote-cleanup-batches/batch-c-ambiguous-stale.json',
      auditJson: 'tmp/maintenance/remote-cleanup-reference-audit/batch-c-ambiguous-stale.audit.json',
      outputDir: 'tmp/maintenance/remote-cleanup-ambiguous-evidence',
    });

    const sandbox = mkdtempSync(join(tmpdir(), 'ae-remote-cleanup-ambiguous-evidence-'));
    const batchJsonPath = join(sandbox, 'batch-c.json');
    const auditJsonPath = join(sandbox, 'batch-c.audit.json');
    const outputDir = join(sandbox, 'out');

    try {
      writeFileSync(batchJsonPath, `${JSON.stringify(createBatchPayload(), null, 2)}\n`);
      writeFileSync(auditJsonPath, `${JSON.stringify(createAuditPayload(), null, 2)}\n`);

      const result = spawnSync(
        'node',
        [scriptPath, '--batch-json', batchJsonPath, '--audit-json', auditJsonPath, '--output-dir', outputDir],
        { cwd: repoRoot, encoding: 'utf8', timeout: 120_000 },
      );

      expect(result.status, result.stderr || result.stdout).toBe(0);
      expect(result.stdout).toContain('total=2 keep=1 manual=1');

      const summary = JSON.parse(readFileSync(join(outputDir, 'summary.json'), 'utf8'));
      expect(summary.counts.total).toBe(2);
      expect(summary.counts.reviewHints['keep-review']).toBe(1);
      expect(summary.counts.reviewHints['manual-review']).toBe(1);
      expect(summary.counts.withOpenIssueRefs).toBe(1);
      expect(summary.counts.clearOfActiveRefs).toBe(1);

      const csv = readFileSync(join(outputDir, 'ambiguous-evidence.csv'), 'utf8');
      expect(csv).toContain('feature/ambiguous-a');
      expect(csv).toContain('#2401 (merged)');
      expect(csv).toContain('main');

      const issueComment = readFileSync(join(outputDir, 'issue-comment.md'), 'utf8');
      expect(issueComment).toContain('Top rows:');
      expect(issueComment).toContain('feature/ambiguous-a');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('rejects mismatched provenance or branch rows', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-remote-cleanup-ambiguous-evidence-mismatch-'));
    const batchJsonPath = join(sandbox, 'batch-c.json');
    const auditJsonPath = join(sandbox, 'batch-c.audit.json');
    const outputDir = join(sandbox, 'out');

    try {
      const batchPayload = createBatchPayload();
      const auditPayload = createAuditPayload();
      auditPayload.sourceTriage.base = 'origin/release';
      auditPayload.items[1].branchOid = 'oid-b-mismatch';
      writeFileSync(batchJsonPath, `${JSON.stringify(batchPayload, null, 2)}\n`);
      writeFileSync(auditJsonPath, `${JSON.stringify(auditPayload, null, 2)}\n`);

      const result = spawnSync(
        'node',
        [scriptPath, '--batch-json', batchJsonPath, '--audit-json', auditJsonPath, '--output-dir', outputDir],
        { cwd: repoRoot, encoding: 'utf8', timeout: 120_000 },
      );

      expect(result.status).not.toBe(0);
      expect(result.stderr || result.stdout).toContain('sourceTriage.base mismatch');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('handles ambiguous rows with no surviving references', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-remote-cleanup-ambiguous-evidence-clear-'));
    const batchJsonPath = join(sandbox, 'batch-c.json');
    const auditJsonPath = join(sandbox, 'batch-c.audit.json');
    const outputDir = join(sandbox, 'out');

    try {
      const batchPayload = createBatchPayload();
      batchPayload.items = [batchPayload.items[1]];
      batchPayload.count = 1;

      const auditPayload = createAuditPayload();
      auditPayload.items = [auditPayload.items[1]];
      auditPayload.summary = {
        total: 1,
        withOpenIssueRefs: 0,
        withAutomationRefs: 0,
        withPlanRefs: 0,
        withCodeRefs: 0,
        clearCandidates: 1,
      };

      writeFileSync(batchJsonPath, `${JSON.stringify(batchPayload, null, 2)}\n`);
      writeFileSync(auditJsonPath, `${JSON.stringify(auditPayload, null, 2)}\n`);

      const result = spawnSync(
        'node',
        [scriptPath, '--batch-json', batchJsonPath, '--audit-json', auditJsonPath, '--output-dir', outputDir],
        { cwd: repoRoot, encoding: 'utf8', timeout: 120_000 },
      );

      expect(result.status, result.stderr || result.stdout).toBe(0);
      const summary = JSON.parse(readFileSync(join(outputDir, 'summary.json'), 'utf8'));
      expect(summary.counts.total).toBe(1);
      expect(summary.counts.clearOfActiveRefs).toBe(1);
      expect(summary.items[0]).toMatchObject({
        branch: 'docs/ambiguous-b',
        reviewHint: 'manual-review',
      });
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });

  it('rejects mismatched reported totals and invalid ageDays values', () => {
    const sandbox = mkdtempSync(join(tmpdir(), 'ae-remote-cleanup-ambiguous-evidence-invalid-'));
    const batchJsonPath = join(sandbox, 'batch-c.json');
    const auditJsonPath = join(sandbox, 'batch-c.audit.json');
    const outputDir = join(sandbox, 'out');

    try {
      const batchPayload = createBatchPayload();
      batchPayload.count = 99;
      const auditPayload = createAuditPayload();
      writeFileSync(batchJsonPath, `${JSON.stringify(batchPayload, null, 2)}\n`);
      writeFileSync(auditJsonPath, `${JSON.stringify(auditPayload, null, 2)}\n`);

      const mismatchedTotal = spawnSync(
        'node',
        [scriptPath, '--batch-json', batchJsonPath, '--audit-json', auditJsonPath, '--output-dir', outputDir],
        { cwd: repoRoot, encoding: 'utf8', timeout: 120_000 },
      );

      expect(mismatchedTotal.status).not.toBe(0);
      expect(mismatchedTotal.stderr || mismatchedTotal.stdout).toContain('batch JSON count mismatch');

      batchPayload.count = batchPayload.items.length;
      batchPayload.items[0].ageDays = 'not-a-number';
      writeFileSync(batchJsonPath, `${JSON.stringify(batchPayload, null, 2)}\n`);

      const invalidAge = spawnSync(
        'node',
        [scriptPath, '--batch-json', batchJsonPath, '--audit-json', auditJsonPath, '--output-dir', outputDir],
        { cwd: repoRoot, encoding: 'utf8', timeout: 120_000 },
      );

      expect(invalidAge.status).not.toBe(0);
      expect(invalidAge.stderr || invalidAge.stdout).toContain('Invalid ageDays value for branch feature/ambiguous-a');
    } finally {
      rmSync(sandbox, { recursive: true, force: true });
    }
  });
});
