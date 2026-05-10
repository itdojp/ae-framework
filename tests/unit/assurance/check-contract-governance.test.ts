import { afterEach, beforeEach, describe, expect, it } from 'vitest';
import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import { spawnSync } from 'node:child_process';

const repoRoot = process.cwd();
const scriptPath = join(repoRoot, 'scripts', 'assurance', 'check-contract-governance.mjs');

function writeText(root: string, relativePath: string, text: string): void {
  const absolutePath = join(root, relativePath);
  mkdirSync(dirname(absolutePath), { recursive: true });
  writeFileSync(absolutePath, text);
}

function writeValidGovernanceDocs(root: string): void {
  writeText(
    root,
    'docs/reference/SCHEMA-GOVERNANCE.md',
    [
      '# Schema Governance',
      '## Dual-write / dual-validate migration rules',
      '## Breaking-change checklist',
      '- migration note',
      '- contract catalog update'
    ].join('\n'),
  );
  writeText(
    root,
    'docs/reference/CONTRACT-CATALOG.md',
    [
      '# Contract Catalog',
      'Link: docs/reference/ASSURANCE-CANONICAL-ROUTES.md',
      '## Current cleanup markers',
      'preview legacy compatibility'
    ].join('\n'),
  );
  writeText(
    root,
    'docs/reference/ASSURANCE-CANONICAL-ROUTES.md',
    [
      '# Assurance Canonical Routes',
      '## Compatibility rules',
      '## Cleanup backlog',
      'Quality scorecard',
      'Formal evidence status',
      'Counterexample GWT summary',
      'Change package'
    ].join('\n'),
  );
  writeText(
    root,
    'docs/reports/ASSURANCE-CONTROL-PLANE-CURRENT-STATE.md',
    [
      '# Current State',
      '`ready`',
      '`partial`',
      '`preview`',
      '`missing`',
      '`duplicate`',
      '`obsolete`'
    ].join('\n'),
  );
}

function runCheck(root: string, ...extraArgs: string[]) {
  return spawnSync(process.execPath, [scriptPath, '--root', root, ...extraArgs], {
    cwd: repoRoot,
    encoding: 'utf8',
  });
}

describe('check-contract-governance', () => {
  let workdir: string;

  beforeEach(() => {
    workdir = mkdtempSync(join(tmpdir(), 'ae-contract-governance-'));
  });

  afterEach(() => {
    rmSync(workdir, { recursive: true, force: true });
  });

  it('passes when required governance markers are present', () => {
    writeValidGovernanceDocs(workdir);

    const result = runCheck(workdir);

    expect(result.status, result.stderr || result.stdout).toBe(0);
    expect(result.stdout).toContain('Assurance contract governance check');
    expect(result.stdout).toContain('- failures: 0');
  });

  it('fails with clear missing marker output', () => {
    writeValidGovernanceDocs(workdir);
    writeText(
      workdir,
      'docs/reference/ASSURANCE-CANONICAL-ROUTES.md',
      [
        '# Assurance Canonical Routes',
        '## Compatibility rules',
        'Quality scorecard'
      ].join('\n'),
    );

    const result = runCheck(workdir);

    expect(result.status).toBe(1);
    expect(result.stdout).toContain('canonical-routes-compatibility-rules');
    expect(result.stdout).toContain('missing marker: Cleanup backlog');
    expect(result.stdout).toContain('missing marker: Formal evidence status');
  });

  it('emits machine-readable JSON for CI consumers', () => {
    writeValidGovernanceDocs(workdir);

    const result = runCheck(workdir, '--json');

    expect(result.status, result.stderr || result.stdout).toBe(0);
    const payload = JSON.parse(result.stdout) as { ok: boolean; checks: unknown[]; failures: unknown[] };
    expect(payload.ok).toBe(true);
    expect(payload.checks).toHaveLength(4);
    expect(payload.failures).toHaveLength(0);
  });
});
