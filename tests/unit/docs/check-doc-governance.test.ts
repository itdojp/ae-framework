import { mkdtempSync, mkdirSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import path from 'node:path';

import { afterEach, describe, expect, it } from 'vitest';

import { main } from '../../../scripts/docs/check-doc-governance.mjs';

const tempRoots: string[] = [];

function makeRoot() {
  const rootDir = mkdtempSync(path.join(tmpdir(), 'ae-doc-governance-'));
  mkdirSync(path.join(rootDir, 'docs', 'agents'), { recursive: true });
  mkdirSync(path.join(rootDir, 'docs', 'architecture'), { recursive: true });
  mkdirSync(path.join(rootDir, 'docs', 'ci'), { recursive: true });
  mkdirSync(path.join(rootDir, 'docs', 'contributing'), { recursive: true });
  mkdirSync(path.join(rootDir, 'docs', 'development'), { recursive: true });
  mkdirSync(path.join(rootDir, 'docs', 'flows'), { recursive: true });
  mkdirSync(path.join(rootDir, 'docs', 'getting-started'), { recursive: true });
  mkdirSync(path.join(rootDir, 'docs', 'guides'), { recursive: true });
  mkdirSync(path.join(rootDir, 'docs', 'handoff'), { recursive: true });
  mkdirSync(path.join(rootDir, 'docs', 'integrations'), { recursive: true });
  mkdirSync(path.join(rootDir, 'docs', 'maintenance'), { recursive: true });
  mkdirSync(path.join(rootDir, 'docs', 'observability'), { recursive: true });
  mkdirSync(path.join(rootDir, 'docs', 'operate'), { recursive: true });
  mkdirSync(path.join(rootDir, 'docs', 'operations'), { recursive: true });
  mkdirSync(path.join(rootDir, 'docs', 'phases'), { recursive: true });
  mkdirSync(path.join(rootDir, 'docs', 'product'), { recursive: true });
  mkdirSync(path.join(rootDir, 'docs', 'project'), { recursive: true });
  mkdirSync(path.join(rootDir, 'docs', 'quality'), { recursive: true });
  mkdirSync(path.join(rootDir, 'docs', 'reference'), { recursive: true });
  mkdirSync(path.join(rootDir, 'docs', 'samples'), { recursive: true });
  mkdirSync(path.join(rootDir, 'docs', 'spec'), { recursive: true });
  mkdirSync(path.join(rootDir, 'docs', 'strategy'), { recursive: true });
  mkdirSync(path.join(rootDir, 'docs', 'testing'), { recursive: true });
  mkdirSync(path.join(rootDir, 'docs', 'trace'), { recursive: true });
  mkdirSync(path.join(rootDir, 'docs', 'troubleshooting'), { recursive: true });
  mkdirSync(path.join(rootDir, 'docs', 'verify'), { recursive: true });
  mkdirSync(path.join(rootDir, 'docs', 'workflows'), { recursive: true });
  tempRoots.push(rootDir);
  return rootDir;
}

function writeMarkdown(rootDir: string, relativePath: string, content: string) {
  writeFileSync(path.join(rootDir, relativePath), content, 'utf8');
}

function withCapturedOutput(fn: () => number) {
  const stdout: string[] = [];
  const stderr: string[] = [];
  const originalStdout = process.stdout.write;
  const originalStderr = process.stderr.write;

  process.stdout.write = ((chunk: unknown) => {
    stdout.push(String(chunk));
    return true;
  }) as typeof process.stdout.write;

  process.stderr.write = ((chunk: unknown) => {
    stderr.push(String(chunk));
    return true;
  }) as typeof process.stderr.write;

  try {
    return {
      exitCode: fn(),
      stdout: stdout.join(''),
      stderr: stderr.join(''),
    };
  } finally {
    process.stdout.write = originalStdout;
    process.stderr.write = originalStderr;
  }
}

afterEach(() => {
  while (tempRoots.length > 0) {
    const rootDir = tempRoots.pop();
    if (rootDir) {
      rmSync(rootDir, { recursive: true, force: true });
    }
  }
});

describe('check-doc-governance', () => {
  it('reports warnings for narrative docs without failing the run', () => {
    const rootDir = makeRoot();

    writeMarkdown(rootDir, 'README.md', [
      '---',
      'docRole: narrative',
      'lastVerified: 2026-03-09',
      '---',
      '',
      '# Root',
      '',
      'This guide must explain the baseline path.',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'AGENTS.md', [
      '---',
      'docRole: derived',
      'canonicalSource:',
      '  - docs/agents/agents-doc-boundary-matrix.md',
      'lastVerified: 2026-03-09',
      '---',
      '',
      '# Agents',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/README.md', [
      '---',
      'docRole: narrative',
      'lastVerified: 2026-03-09',
      '---',
      '',
      '# Docs',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/agents/agents-doc-boundary-matrix.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-09',
      'owner: agent-ops',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Matrix',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/agents/README.md', [
      '---',
      'docRole: derived',
      'canonicalSource:',
      '  - docs/agents/agents-doc-boundary-matrix.md',
      'lastVerified: 2026-03-09',
      '---',
      '',
      '# Agent Docs',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/reference/DOC-GOVERNANCE.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-09',
      'owner: docs-governance',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Governance',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/project/RELEASE.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-10',
      'owner: release-ops',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Release',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/operate/monitor.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-10',
      'owner: observability-ops',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Monitor',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/getting-started/SETUP.md', [
      '---',
      'docRole: derived',
      'canonicalSource:',
      '  - README.md',
      '  - docs/quality/assurance-operations-runbook.md',
      'lastVerified: 2026-03-10',
      '---',
      '',
      '# Setup',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/quality/assurance-operations-runbook.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-10',
      'owner: quality-ops',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Assurance Ops',
      '',
    ].join('\n'));

    const result = withCapturedOutput(() => main([
      'node',
      'scripts/docs/check-doc-governance.mjs',
      '--root',
      rootDir,
      '--format=json',
    ]));

    expect(result.exitCode).toBe(0);
    const payload = JSON.parse(result.stdout);
    expect(payload.docsScanned).toBe(10);
    expect(payload.failures).toEqual([]);
    expect(payload.warnings).toHaveLength(1);
    expect(payload.warnings[0].markdownPath).toBe('README.md');
    expect(result.stderr).toBe('');
  });

  it('governs docs/project and docs/operate files', () => {
    const rootDir = makeRoot();

    writeMarkdown(rootDir, 'README.md', [
      '---',
      'docRole: narrative',
      'lastVerified: 2026-03-10',
      '---',
      '',
      '# Root',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'AGENTS.md', [
      '---',
      'docRole: derived',
      'canonicalSource:',
      '  - docs/agents/agents-doc-boundary-matrix.md',
      'lastVerified: 2026-03-10',
      '---',
      '',
      '# Agents',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/README.md', [
      '---',
      'docRole: narrative',
      'lastVerified: 2026-03-10',
      '---',
      '',
      '# Docs',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/agents/agents-doc-boundary-matrix.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-10',
      'owner: agent-ops',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Matrix',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/reference/DOC-GOVERNANCE.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-10',
      'owner: docs-governance',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Governance',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/project/GOVERNANCE.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-10',
      'owner: project-governance',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Project Governance',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/operate/release-engineering.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-10',
      'owner: release-ops',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Release Engineering',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/getting-started/QUICK-START-GUIDE.md', [
      '---',
      'docRole: derived',
      'canonicalSource:',
      '  - README.md',
      '  - docs/guides/assurance-onboarding-checklist.md',
      'lastVerified: 2026-03-10',
      '---',
      '',
      '# Quick Start',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/guides/assurance-onboarding-checklist.md', [
      '---',
      'docRole: derived',
      'canonicalSource:',
      '  - docs/quality/assurance-operations-runbook.md',
      'lastVerified: 2026-03-10',
      '---',
      '',
      '# Onboarding',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/quality/assurance-operations-runbook.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-10',
      'owner: quality-ops',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Assurance Ops',
      '',
    ].join('\n'));

    const result = withCapturedOutput(() => main([
      'node',
      'scripts/docs/check-doc-governance.mjs',
      '--root',
      rootDir,
      '--format=json',
    ]));

    expect(result.exitCode).toBe(0);
    const payload = JSON.parse(result.stdout);
    expect(payload.failures).toEqual([]);
    expect(payload.warnings).toHaveLength(0);
    expect(payload.docsScanned).toBe(10);
  });

  it('governs docs/integrations files', () => {
    const rootDir = makeRoot();

    writeMarkdown(rootDir, 'README.md', [
      '---',
      'docRole: narrative',
      'lastVerified: 2026-03-10',
      '---',
      '',
      '# Root',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'AGENTS.md', [
      '---',
      'docRole: derived',
      'canonicalSource:',
      '  - docs/agents/agents-doc-boundary-matrix.md',
      'lastVerified: 2026-03-10',
      '---',
      '',
      '# Agents',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/README.md', [
      '---',
      'docRole: narrative',
      'lastVerified: 2026-03-10',
      '---',
      '',
      '# Docs',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/agents/agents-doc-boundary-matrix.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-10',
      'owner: agent-ops',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Matrix',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/reference/DOC-GOVERNANCE.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-10',
      'owner: docs-governance',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Governance',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/integrations/CODEX-INTEGRATION.md', [
      '---',
      'docRole: derived',
      'canonicalSource:',
      '  - README.md',
      '  - docs/agents/commands.md',
      'lastVerified: 2026-03-10',
      '---',
      '',
      '# Codex Integration',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/agents/commands.md', [
      '---',
      'docRole: derived',
      'canonicalSource:',
      '  - docs/agents/agents-doc-boundary-matrix.md',
      'lastVerified: 2026-03-10',
      '---',
      '',
      '# Commands',
      '',
    ].join('\n'));

    const result = withCapturedOutput(() => main([
      'node',
      'scripts/docs/check-doc-governance.mjs',
      '--root',
      rootDir,
      '--format=json',
    ]));

    expect(result.exitCode).toBe(0);
    const payload = JSON.parse(result.stdout);
    expect(payload.failures).toEqual([]);
    expect(payload.warnings).toHaveLength(0);
    expect(payload.docsScanned).toBe(7);
  });

  it('governs docs/maintenance files', () => {
    const rootDir = makeRoot();

    writeMarkdown(rootDir, 'README.md', [
      '---',
      'docRole: narrative',
      'lastVerified: 2026-03-11',
      '---',
      '',
      '# Root',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'AGENTS.md', [
      '---',
      'docRole: derived',
      'canonicalSource:',
      '  - docs/agents/agents-doc-boundary-matrix.md',
      'lastVerified: 2026-03-11',
      '---',
      '',
      '# Agents',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/README.md', [
      '---',
      'docRole: narrative',
      'lastVerified: 2026-03-11',
      '---',
      '',
      '# Docs',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/agents/agents-doc-boundary-matrix.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-11',
      'owner: agent-ops',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Matrix',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/reference/DOC-GOVERNANCE.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-11',
      'owner: docs-governance',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Governance',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/maintenance/repo-layout-policy.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-11',
      'owner: repo-maintenance',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Repo Layout',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/maintenance/branch-cleanup-report-2026-02-28.md', [
      '---',
      'docRole: narrative',
      'lastVerified: 2026-03-11',
      '---',
      '',
      '# Branch Cleanup Report',
      '',
    ].join('\n'));

    const result = withCapturedOutput(() => main([
      'node',
      'scripts/docs/check-doc-governance.mjs',
      '--root',
      rootDir,
      '--format=json',
    ]));

    expect(result.exitCode).toBe(0);
    const payload = JSON.parse(result.stdout);
    expect(payload.failures).toEqual([]);
    expect(payload.warnings).toHaveLength(0);
    expect(payload.docsScanned).toBe(7);
  });

  it('governs docs/trace files', () => {
    const rootDir = makeRoot();

    writeMarkdown(rootDir, 'README.md', [
      '---',
      'docRole: narrative',
      'lastVerified: 2026-03-11',
      '---',
      '',
      '# Root',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'AGENTS.md', [
      '---',
      'docRole: derived',
      'canonicalSource:',
      '  - docs/agents/agents-doc-boundary-matrix.md',
      'lastVerified: 2026-03-11',
      '---',
      '',
      '# Agents',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/README.md', [
      '---',
      'docRole: narrative',
      'lastVerified: 2026-03-11',
      '---',
      '',
      '# Docs',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/agents/agents-doc-boundary-matrix.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-11',
      'owner: agent-ops',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Matrix',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/reference/DOC-GOVERNANCE.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-11',
      'owner: docs-governance',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Governance',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/trace/REPORT_ENVELOPE.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-11',
      'owner: trace-ops',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Report Envelope',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/trace/multi-domain-roadmap.md', [
      '---',
      'docRole: narrative',
      'lastVerified: 2026-03-11',
      '---',
      '',
      '# Trace Roadmap',
      '',
    ].join('\n'));

    const result = withCapturedOutput(() => main([
      'node',
      'scripts/docs/check-doc-governance.mjs',
      '--root',
      rootDir,
      '--format=json',
    ]));

    expect(result.exitCode).toBe(0);
    const payload = JSON.parse(result.stdout);
    expect(payload.failures).toEqual([]);
    expect(payload.warnings).toHaveLength(0);
    expect(payload.docsScanned).toBe(7);
  });

  it('governs docs/phases files', () => {
    const rootDir = makeRoot();

    writeMarkdown(rootDir, 'README.md', [
      '---',
      'docRole: narrative',
      'lastVerified: 2026-03-10',
      '---',
      '',
      '# Root',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'AGENTS.md', [
      '---',
      'docRole: derived',
      'canonicalSource:',
      '  - docs/agents/agents-doc-boundary-matrix.md',
      'lastVerified: 2026-03-10',
      '---',
      '',
      '# Agents',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/README.md', [
      '---',
      'docRole: narrative',
      'lastVerified: 2026-03-10',
      '---',
      '',
      '# Docs',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/agents/agents-doc-boundary-matrix.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-10',
      'owner: agent-ops',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Matrix',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/reference/DOC-GOVERNANCE.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-10',
      'owner: docs-governance',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Governance',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/phases/PHASE-4-VALIDATION.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-10',
      'owner: phase-docs',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Validation',
      '',
    ].join('\n'));

    const result = withCapturedOutput(() => main([
      'node',
      'scripts/docs/check-doc-governance.mjs',
      '--root',
      rootDir,
      '--format=json',
    ]));

    expect(result.exitCode).toBe(0);
    const payload = JSON.parse(result.stdout);
    expect(payload.failures).toEqual([]);
    expect(payload.warnings).toEqual([]);
  });

  it('governs docs/testing files', () => {
    const rootDir = makeRoot();

    writeMarkdown(rootDir, 'README.md', [
      '---',
      'docRole: narrative',
      'lastVerified: 2026-03-10',
      '---',
      '',
      '# Root',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'AGENTS.md', [
      '---',
      'docRole: derived',
      'canonicalSource:',
      '  - docs/agents/agents-doc-boundary-matrix.md',
      'lastVerified: 2026-03-10',
      '---',
      '',
      '# Agents',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/README.md', [
      '---',
      'docRole: narrative',
      'lastVerified: 2026-03-10',
      '---',
      '',
      '# Docs',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/agents/agents-doc-boundary-matrix.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-10',
      'owner: agent-ops',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Matrix',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/reference/DOC-GOVERNANCE.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-10',
      'owner: docs-governance',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Governance',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/testing/replay-runner.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-10',
      'owner: testing-docs',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Replay Runner',
      '',
    ].join('\n'));

    const result = withCapturedOutput(() => main([
      'node',
      'scripts/docs/check-doc-governance.mjs',
      '--root',
      rootDir,
      '--format=json',
    ]));

    expect(result.exitCode).toBe(0);
    const payload = JSON.parse(result.stdout);
    expect(payload.failures).toEqual([]);
    expect(payload.warnings).toEqual([]);
  });

  it('governs docs/handoff files', () => {
    const rootDir = makeRoot();

    writeMarkdown(rootDir, 'README.md', [
      '---',
      'docRole: narrative',
      'lastVerified: 2026-03-10',
      '---',
      '',
      '# Root',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'AGENTS.md', [
      '---',
      'docRole: derived',
      'canonicalSource:',
      '  - docs/agents/agents-doc-boundary-matrix.md',
      'lastVerified: 2026-03-10',
      '---',
      '',
      '# Agents',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/README.md', [
      '---',
      'docRole: narrative',
      'lastVerified: 2026-03-10',
      '---',
      '',
      '# Docs',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/agents/agents-doc-boundary-matrix.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-10',
      'owner: agent-ops',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Matrix',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/reference/DOC-GOVERNANCE.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-10',
      'owner: docs-governance',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Governance',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/handoff/README.md', [
      '---',
      'docRole: narrative',
      'lastVerified: 2026-03-10',
      '---',
      '',
      '# Handoff',
      '',
    ].join('\n'));

    const result = withCapturedOutput(() => main([
      'node',
      'scripts/docs/check-doc-governance.mjs',
      '--root',
      rootDir,
      '--format=json',
    ]));

    expect(result.exitCode).toBe(0);
    const payload = JSON.parse(result.stdout);
    expect(payload.docsScanned).toBe(6);
    expect(payload.failures).toEqual([]);
    expect(payload.warnings).toEqual([]);
  });

  it('governs docs/verify files', () => {
    const rootDir = makeRoot();

    writeMarkdown(rootDir, 'README.md', [
      '---',
      'docRole: narrative',
      'lastVerified: 2026-03-11',
      '---',
      '',
      '# Root',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'AGENTS.md', [
      '---',
      'docRole: derived',
      'canonicalSource:',
      '  - docs/agents/agents-doc-boundary-matrix.md',
      'lastVerified: 2026-03-11',
      '---',
      '',
      '# Agents',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/README.md', [
      '---',
      'docRole: narrative',
      'lastVerified: 2026-03-11',
      '---',
      '',
      '# Docs',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/agents/agents-doc-boundary-matrix.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-11',
      'owner: agent-ops',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Matrix',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/reference/DOC-GOVERNANCE.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-11',
      'owner: docs-governance',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Governance',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/verify/TEST-HARNESS-REPRO.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-11',
      'owner: verify-first',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Verify Repro',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/verify/VERIFY-LITE-2025-10-07.md', [
      '---',
      'docRole: narrative',
      'lastVerified: 2026-03-11',
      '---',
      '',
      '# Verify Lite Summary',
      '',
    ].join('\n'));

    const result = withCapturedOutput(() => main([
      'node',
      'scripts/docs/check-doc-governance.mjs',
      '--root',
      rootDir,
      '--format=json',
    ]));

    expect(result.exitCode).toBe(0);
    const payload = JSON.parse(result.stdout);
    expect(payload.failures).toEqual([]);
    expect(payload.warnings).toHaveLength(0);
    expect(payload.docsScanned).toBe(7);
  });

  it('governs remaining small docs directories', () => {
    const rootDir = makeRoot();

    writeMarkdown(rootDir, 'README.md', [
      '---',
      'docRole: narrative',
      'lastVerified: 2026-03-11',
      '---',
      '',
      '# Root',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'AGENTS.md', [
      '---',
      'docRole: derived',
      'canonicalSource:',
      '  - docs/agents/agents-doc-boundary-matrix.md',
      'lastVerified: 2026-03-11',
      '---',
      '',
      '# Agents',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/README.md', [
      '---',
      'docRole: narrative',
      'lastVerified: 2026-03-11',
      '---',
      '',
      '# Docs',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/agents/agents-doc-boundary-matrix.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-11',
      'owner: agent-ops',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Matrix',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/reference/DOC-GOVERNANCE.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-11',
      'owner: docs-governance',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Governance',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/contributing/PR_TEMPLATE.md', [
      '---',
      'docRole: narrative',
      'lastVerified: 2026-03-11',
      '---',
      '',
      '# PR Template',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/operations/context-pack-troubleshooting.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-11',
      'owner: context-pack-ops',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Context Pack Troubleshooting',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/observability/runtime-guard-dashboard.md', [
      '---',
      'docRole: derived',
      'canonicalSource:',
      '  - docs/operate/monitor.md',
      '  - docs/operate/telemetry-as-context.md',
      'lastVerified: 2026-03-11',
      '---',
      '',
      '# Runtime Guard Dashboard',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/troubleshooting/WINDOWS-INSTALLATION.md', [
      '---',
      'docRole: narrative',
      'lastVerified: 2026-03-11',
      '---',
      '',
      '# Windows Troubleshooting',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/samples/minimal-run.md', [
      '---',
      'docRole: narrative',
      'lastVerified: 2026-03-11',
      '---',
      '',
      '# Minimal Run',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/spec/context-pack.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-11',
      'owner: context-pack-ops',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Context Pack',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/spec/registry.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-11',
      'owner: docs-governance',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Spec Registry',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/operate/monitor.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-11',
      'owner: observability-ops',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Monitor',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/operate/telemetry-as-context.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-11',
      'owner: observability-ops',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Telemetry as Context',
      '',
    ].join('\n'));

    const result = withCapturedOutput(() => main([
      'node',
      'scripts/docs/check-doc-governance.mjs',
      '--root',
      rootDir,
      '--format=json',
    ]));

    expect(result.exitCode).toBe(0);
    const payload = JSON.parse(result.stdout);
    expect(payload.failures).toEqual([]);
    expect(payload.warnings).toHaveLength(0);
    expect(payload.docsScanned).toBe(14);
  });

  it('governs docs/architecture files', () => {
    const rootDir = makeRoot();

    writeMarkdown(rootDir, 'README.md', [
      '---',
      'docRole: narrative',
      'lastVerified: 2026-03-11',
      '---',
      '',
      '# Root',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'AGENTS.md', [
      '---',
      'docRole: derived',
      'canonicalSource:',
      '  - docs/agents/agents-doc-boundary-matrix.md',
      'lastVerified: 2026-03-11',
      '---',
      '',
      '# Agents',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/README.md', [
      '---',
      'docRole: narrative',
      'lastVerified: 2026-03-11',
      '---',
      '',
      '# Docs',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/agents/agents-doc-boundary-matrix.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-11',
      'owner: agent-ops',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Matrix',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/reference/DOC-GOVERNANCE.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-11',
      'owner: docs-governance',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Governance',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/architecture/CURRENT-SYSTEM-OVERVIEW.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-11',
      'owner: architecture-docs',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Current Overview',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/architecture/ARCHITECTURE.md', [
      '---',
      'docRole: narrative',
      'lastVerified: 2026-03-11',
      '---',
      '',
      '# Architecture',
      '',
    ].join('\n'));

    const result = withCapturedOutput(() => main([
      'node',
      'scripts/docs/check-doc-governance.mjs',
      '--root',
      rootDir,
      '--format=json',
    ]));

    expect(result.exitCode).toBe(0);
    const payload = JSON.parse(result.stdout);
    expect(payload.failures).toEqual([]);
    expect(payload.warnings).toHaveLength(0);
    expect(payload.docsScanned).toBe(7);
  });

  it('governs docs/guides files', () => {
    const rootDir = makeRoot();

    writeMarkdown(rootDir, 'README.md', [
      '---',
      'docRole: narrative',
      'lastVerified: 2026-03-10',
      '---',
      '',
      '# Root',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'AGENTS.md', [
      '---',
      'docRole: derived',
      'canonicalSource:',
      '  - docs/agents/agents-doc-boundary-matrix.md',
      'lastVerified: 2026-03-10',
      '---',
      '',
      '# Agents',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/README.md', [
      '---',
      'docRole: narrative',
      'lastVerified: 2026-03-10',
      '---',
      '',
      '# Docs',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/agents/agents-doc-boundary-matrix.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-10',
      'owner: agent-ops',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Matrix',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/reference/DOC-GOVERNANCE.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-10',
      'owner: docs-governance',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Governance',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/guides/USAGE.md', [
      '---',
      'docRole: derived',
      'canonicalSource:',
      '  - README.md',
      '  - docs/getting-started/QUICK-START-GUIDE.md',
      'lastVerified: 2026-03-10',
      '---',
      '',
      '# Usage',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/getting-started/QUICK-START-GUIDE.md', [
      '---',
      'docRole: derived',
      'canonicalSource:',
      '  - README.md',
      '  - docs/quality/assurance-operations-runbook.md',
      'lastVerified: 2026-03-10',
      '---',
      '',
      '# Quick Start',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/quality/assurance-operations-runbook.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-10',
      'owner: quality-ops',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Assurance Ops',
      '',
    ].join('\n'));

    const result = withCapturedOutput(() => main([
      'node',
      'scripts/docs/check-doc-governance.mjs',
      '--root',
      rootDir,
      '--format=json',
    ]));

    expect(result.exitCode).toBe(0);
    const payload = JSON.parse(result.stdout);
    expect(payload.failures).toEqual([]);
    expect(payload.warnings).toHaveLength(0);
    expect(payload.docsScanned).toBe(8);
  });

  it('governs docs/reference files without double-counting DOC-GOVERNANCE', () => {
    const rootDir = makeRoot();

    writeMarkdown(rootDir, 'README.md', [
      '---',
      'docRole: narrative',
      'lastVerified: 2026-03-10',
      '---',
      '',
      '# Root',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'AGENTS.md', [
      '---',
      'docRole: derived',
      'canonicalSource:',
      '  - docs/agents/agents-doc-boundary-matrix.md',
      'lastVerified: 2026-03-10',
      '---',
      '',
      '# Agents',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/README.md', [
      '---',
      'docRole: narrative',
      'lastVerified: 2026-03-10',
      '---',
      '',
      '# Docs',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/agents/agents-doc-boundary-matrix.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-10',
      'owner: agent-ops',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Matrix',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/reference/DOC-GOVERNANCE.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-10',
      'owner: docs-governance',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Governance',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/reference/API.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-10',
      'owner: docs-governance',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# API',
      '',
    ].join('\n'));

    const result = withCapturedOutput(() => main([
      'node',
      'scripts/docs/check-doc-governance.mjs',
      '--root',
      rootDir,
      '--format=json',
    ]));

    expect(result.exitCode).toBe(0);
    const payload = JSON.parse(result.stdout);
    expect(payload.failures).toEqual([]);
    expect(payload.warnings).toHaveLength(0);
    expect(payload.docsScanned).toBe(6);
  });

  it('governs docs/workflows files', () => {
    const rootDir = makeRoot();

    writeMarkdown(rootDir, 'README.md', [
      '---',
      'docRole: narrative',
      'lastVerified: 2026-03-11',
      '---',
      '',
      '# Root',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'AGENTS.md', [
      '---',
      'docRole: derived',
      'canonicalSource:',
      '  - docs/agents/agents-doc-boundary-matrix.md',
      'lastVerified: 2026-03-11',
      '---',
      '',
      '# Agents',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/README.md', [
      '---',
      'docRole: narrative',
      'lastVerified: 2026-03-11',
      '---',
      '',
      '# Docs',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/agents/agents-doc-boundary-matrix.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-11',
      'owner: agent-ops',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Matrix',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/reference/DOC-GOVERNANCE.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-11',
      'owner: docs-governance',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Governance',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/reference/SCHEMA-GOVERNANCE.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-11',
      'owner: docs-governance',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Schema Governance',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/reference/SPEC-VERIFICATION-KIT-EXTENSIONS.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-11',
      'owner: docs-governance',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Spec Verification Kit Extensions',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/workflows/NL-to-AE-Spec-Workflow.md', [
      '---',
      'docRole: derived',
      'canonicalSource:',
      '  - docs/reference/SCHEMA-GOVERNANCE.md',
      '  - docs/reference/SPEC-VERIFICATION-KIT-EXTENSIONS.md',
      'lastVerified: 2026-03-11',
      '---',
      '',
      '# Workflow',
      '',
    ].join('\n'));

    const result = withCapturedOutput(() => main([
      'node',
      'scripts/docs/check-doc-governance.mjs',
      '--root',
      rootDir,
      '--format=json',
    ]));

    expect(result.exitCode).toBe(0);
    const payload = JSON.parse(result.stdout);
    expect(payload.failures).toEqual([]);
    expect(payload.warnings).toHaveLength(0);
    expect(payload.docsScanned).toBe(8);
  });

  it('governs docs/ci files', () => {
    const rootDir = makeRoot();

    writeMarkdown(rootDir, 'README.md', [
      '---',
      'docRole: narrative',
      'lastVerified: 2026-03-10',
      '---',
      '',
      '# Root',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'AGENTS.md', [
      '---',
      'docRole: derived',
      'canonicalSource:',
      '  - docs/agents/agents-doc-boundary-matrix.md',
      'lastVerified: 2026-03-10',
      '---',
      '',
      '# Agents',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/README.md', [
      '---',
      'docRole: narrative',
      'lastVerified: 2026-03-10',
      '---',
      '',
      '# Docs',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/agents/agents-doc-boundary-matrix.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-10',
      'owner: agent-ops',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Matrix',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/reference/DOC-GOVERNANCE.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-10',
      'owner: docs-governance',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Governance',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/ci/policy.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-10',
      'owner: quality-ops',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# CI Policy',
      '',
    ].join('\n'));

    const result = withCapturedOutput(() => main([
      'node',
      'scripts/docs/check-doc-governance.mjs',
      '--root',
      rootDir,
      '--format=json',
    ]));

    expect(result.exitCode).toBe(0);
    const payload = JSON.parse(result.stdout);
    expect(payload.docsScanned).toBe(6);
    expect(payload.failures).toEqual([]);
  });

  it('governs docs/strategy files', () => {
    const rootDir = makeRoot();

    writeMarkdown(rootDir, 'README.md', [
      '---',
      'docRole: narrative',
      'lastVerified: 2026-03-11',
      '---',
      '',
      '# Root',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'AGENTS.md', [
      '---',
      'docRole: derived',
      'canonicalSource:',
      '  - docs/agents/agents-doc-boundary-matrix.md',
      'lastVerified: 2026-03-11',
      '---',
      '',
      '# Agents',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/README.md', [
      '---',
      'docRole: narrative',
      'lastVerified: 2026-03-11',
      '---',
      '',
      '# Docs',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/agents/agents-doc-boundary-matrix.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-11',
      'owner: agent-ops',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Matrix',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/reference/DOC-GOVERNANCE.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-11',
      'owner: docs-governance',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Governance',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/strategy/CODEX-AE-BOUNDARY-VERIFY-FIRST.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-11',
      'owner: product-strategy',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Strategy',
      '',
    ].join('\n'));

    const result = withCapturedOutput(() => main([
      'node',
      'scripts/docs/check-doc-governance.mjs',
      '--root',
      rootDir,
      '--format=json',
    ]));

    expect(result.exitCode).toBe(0);
    const payload = JSON.parse(result.stdout);
    expect(payload.failures).toEqual([]);
    expect(payload.warnings).toHaveLength(0);
    expect(payload.docsScanned).toBe(6);
  });

  it('governs docs/flows files', () => {
    const rootDir = makeRoot();

    writeMarkdown(rootDir, 'README.md', [
      '---',
      'docRole: narrative',
      'lastVerified: 2026-03-11',
      '---',
      '',
      '# Root',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'AGENTS.md', [
      '---',
      'docRole: derived',
      'canonicalSource:',
      '  - docs/agents/agents-doc-boundary-matrix.md',
      'lastVerified: 2026-03-11',
      '---',
      '',
      '# Agents',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/README.md', [
      '---',
      'docRole: narrative',
      'lastVerified: 2026-03-11',
      '---',
      '',
      '# Docs',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/agents/agents-doc-boundary-matrix.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-11',
      'owner: agent-ops',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Matrix',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/reference/DOC-GOVERNANCE.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-11',
      'owner: docs-governance',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Governance',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/flows/web-api-manual.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-11',
      'owner: delivery-ops',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Flow',
      '',
    ].join('\n'));

    const result = withCapturedOutput(() => main([
      'node',
      'scripts/docs/check-doc-governance.mjs',
      '--root',
      rootDir,
      '--format=json',
    ]));

    expect(result.exitCode).toBe(0);
    const payload = JSON.parse(result.stdout);
    expect(payload.failures).toEqual([]);
    expect(payload.warnings).toHaveLength(0);
    expect(payload.docsScanned).toBe(6);
  });

  it('governs docs/development files', () => {
    const rootDir = makeRoot();

    writeMarkdown(rootDir, 'README.md', [
      '---',
      'docRole: narrative',
      'lastVerified: 2026-03-11',
      '---',
      '',
      '# Root',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'AGENTS.md', [
      '---',
      'docRole: derived',
      'canonicalSource:',
      '  - docs/agents/agents-doc-boundary-matrix.md',
      'lastVerified: 2026-03-11',
      '---',
      '',
      '# Agents',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/README.md', [
      '---',
      'docRole: narrative',
      'lastVerified: 2026-03-11',
      '---',
      '',
      '# Docs',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/agents/agents-doc-boundary-matrix.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-11',
      'owner: agent-ops',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Matrix',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/reference/DOC-GOVERNANCE.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-11',
      'owner: docs-governance',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Governance',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/development/spec-validation.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-11',
      'owner: development-docs',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Development',
      '',
    ].join('\n'));

    const result = withCapturedOutput(() => main([
      'node',
      'scripts/docs/check-doc-governance.mjs',
      '--root',
      rootDir,
      '--format=json',
    ]));

    expect(result.exitCode).toBe(0);
    const payload = JSON.parse(result.stdout);
    expect(payload.failures).toEqual([]);
    expect(payload.warnings).toHaveLength(0);
    expect(payload.docsScanned).toBe(6);
  });

  it('fails when a derived doc omits canonicalSource', () => {
    const rootDir = makeRoot();

    writeMarkdown(rootDir, 'README.md', [
      '---',
      'docRole: narrative',
      'lastVerified: 2026-03-09',
      '---',
      '',
      '# Root',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'AGENTS.md', [
      '---',
      'docRole: derived',
      'lastVerified: 2026-03-09',
      '---',
      '',
      '# Agents',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/README.md', [
      '---',
      'docRole: narrative',
      'lastVerified: 2026-03-09',
      '---',
      '',
      '# Docs',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/agents/agents-doc-boundary-matrix.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-09',
      'owner: agent-ops',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Matrix',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/reference/DOC-GOVERNANCE.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-09',
      'owner: docs-governance',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Governance',
      '',
    ].join('\n'));

    const result = withCapturedOutput(() => main([
      'node',
      'scripts/docs/check-doc-governance.mjs',
      '--root',
      rootDir,
    ]));

    expect(result.exitCode).toBe(1);
    expect(result.stderr).toContain('AGENTS.md: derived docs must declare canonicalSource');
  });

  it('fails with a structured message when YAML front matter is invalid', () => {
    const rootDir = makeRoot();

    writeMarkdown(rootDir, 'README.md', [
      '---',
      'docRole: narrative',
      'lastVerified: 2026-03-09',
      '---',
      '',
      '# Root',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'AGENTS.md', [
      '---',
      'docRole: derived',
      'canonicalSource: [docs/agents/agents-doc-boundary-matrix.md',
      'lastVerified: 2026-03-09',
      '---',
      '',
      '# Agents',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/README.md', [
      '---',
      'docRole: narrative',
      'lastVerified: 2026-03-09',
      '---',
      '',
      '# Docs',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/agents/agents-doc-boundary-matrix.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-09',
      'owner: agent-ops',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Matrix',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/reference/DOC-GOVERNANCE.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-09',
      'owner: docs-governance',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Governance',
      '',
    ].join('\n'));

    const result = withCapturedOutput(() => main([
      'node',
      'scripts/docs/check-doc-governance.mjs',
      '--root',
      rootDir,
    ]));

    expect(result.exitCode).toBe(1);
    expect(result.stderr).toContain('AGENTS.md: invalid YAML front matter');
  });

  it('scans product and quality docs when the directories are present', () => {
    const rootDir = makeRoot();

    writeMarkdown(rootDir, 'README.md', [
      '---',
      'docRole: narrative',
      'lastVerified: 2026-03-10',
      '---',
      '',
      '# Root',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'AGENTS.md', [
      '---',
      'docRole: derived',
      'canonicalSource:',
      '  - docs/agents/agents-doc-boundary-matrix.md',
      'lastVerified: 2026-03-10',
      '---',
      '',
      '# Agents',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/README.md', [
      '---',
      'docRole: narrative',
      'lastVerified: 2026-03-10',
      '---',
      '',
      '# Docs',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/agents/agents-doc-boundary-matrix.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-10',
      'owner: agent-ops',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Matrix',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/quality/ARTIFACTS-CONTRACT.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-10',
      'owner: quality-ops',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Artifacts Contract',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/product/OVERVIEW.md', [
      '---',
      'docRole: derived',
      'canonicalSource:',
      '  - docs/product/ASSURANCE-CONTROL-PLANE.md',
      'lastVerified: 2026-03-10',
      '---',
      '',
      '# Overview',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/product/ASSURANCE-CONTROL-PLANE.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-10',
      'owner: product-architecture',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Assurance Control Plane',
      '',
    ].join('\n'));
    writeMarkdown(rootDir, 'docs/reference/DOC-GOVERNANCE.md', [
      '---',
      'docRole: ssot',
      'lastVerified: 2026-03-10',
      'owner: docs-governance',
      'verificationCommand: pnpm -s run check:doc-consistency',
      '---',
      '',
      '# Governance',
      '',
    ].join('\n'));

    const result = withCapturedOutput(() => main([
      'node',
      'scripts/docs/check-doc-governance.mjs',
      '--root',
      rootDir,
      '--format=json',
    ]));

    expect(result.exitCode).toBe(0);
    const payload = JSON.parse(result.stdout);
    expect(payload.docsScanned).toBe(8);
    expect(payload.failures).toEqual([]);
  });
});
