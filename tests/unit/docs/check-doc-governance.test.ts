import { mkdtempSync, mkdirSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import path from 'node:path';

import { afterEach, describe, expect, it } from 'vitest';

import { main } from '../../../scripts/docs/check-doc-governance.mjs';

const tempRoots: string[] = [];

function makeRoot() {
  const rootDir = mkdtempSync(path.join(tmpdir(), 'ae-doc-governance-'));
  mkdirSync(path.join(rootDir, 'docs', 'agents'), { recursive: true });
  mkdirSync(path.join(rootDir, 'docs', 'product'), { recursive: true });
  mkdirSync(path.join(rootDir, 'docs', 'quality'), { recursive: true });
  mkdirSync(path.join(rootDir, 'docs', 'reference'), { recursive: true });
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
    expect(payload.warnings).toHaveLength(1);
    expect(payload.warnings[0].markdownPath).toBe('README.md');
    expect(result.stderr).toBe('');
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
