import { describe, expect, it, onTestFinished } from 'vitest';
import { chmodSync, existsSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join, resolve } from 'node:path';
import { randomUUID } from 'node:crypto';

const repoRoot = resolve('.');
const scriptPath = resolve(repoRoot, 'scripts/assurance/post-pr-review-surface.mjs');

const runScript = (args: string[]) => spawnSync('node', [scriptPath, ...args], {
  cwd: repoRoot,
  encoding: 'utf8',
  timeout: 120_000,
});

function makeTempRoot(prefix: string) {
  const outputRoot = resolve(repoRoot, 'artifacts', `${prefix}-${randomUUID()}`);
  mkdirSync(outputRoot, { recursive: true });
  onTestFinished(() => {
    rmSync(outputRoot, { recursive: true, force: true });
  });
  return outputRoot;
}

describe('PR review surface posting helper', () => {
  it('defaults to dry-run and prints the target, marker, and comment body without invoking gh', () => {
    const outputRoot = makeTempRoot('pr-review-surface-post-dry-run');
    const bodyFile = join(outputRoot, 'assurance-review.md');
    const body = '# Assurance Review\n\nProducer output is evidence, not approval.\n';
    writeFileSync(bodyFile, body, 'utf8');

    const result = runScript([
      '--repo', 'example/repo',
      '--pr', '42',
      '--body-file', bodyFile,
      '--marker', '<!-- custom-marker -->',
      '--gh-bin', join(outputRoot, 'missing-gh'),
    ]);

    expect(result.status, result.stderr || result.stdout).toBe(0);
    expect(result.stdout).toContain('[assurance-review-surface-post] dry-run');
    expect(result.stdout).toContain('repo: example/repo');
    expect(result.stdout).toContain('pr: 42');
    expect(result.stdout).toContain('marker: <!-- custom-marker -->');
    expect(result.stdout).toContain('--- comment body ---');
    expect(result.stdout).toContain('<!-- custom-marker -->');
    expect(result.stdout).toContain(body.trim());
    expect(readFileSync(bodyFile, 'utf8')).toBe(body);
  });

  it('runs as a CLI when the script path contains spaces', () => {
    const outputRoot = makeTempRoot('pr-review-surface-post-space-path');
    const spacedDir = join(outputRoot, 'path with spaces');
    const copiedScript = join(spacedDir, 'post-pr-review-surface.mjs');
    mkdirSync(spacedDir, { recursive: true });
    writeFileSync(copiedScript, readFileSync(scriptPath, 'utf8'), 'utf8');

    const result = spawnSync('node', [copiedScript, '--help'], {
      cwd: repoRoot,
      encoding: 'utf8',
      timeout: 120_000,
    });

    expect(result.status, result.stderr || result.stdout).toBe(0);
    expect(result.stdout).toContain('Usage: node scripts/assurance/post-pr-review-surface.mjs');
    expect(result.stdout).toContain('--mode <dry-run|comment>');
  });

  it('rejects malformed PR numbers instead of posting to a numeric prefix', () => {
    const outputRoot = makeTempRoot('pr-review-surface-post-bad-pr');
    const bodyFile = join(outputRoot, 'assurance-review.md');
    writeFileSync(bodyFile, '# Review\n', 'utf8');

    for (const value of ['42abc', '1.9', '0']) {
      const result = runScript([
        '--repo', 'example/repo',
        '--pr', value,
        '--body-file', bodyFile,
      ]);

      expect(result.status, value).toBe(1);
      expect(result.stderr).toContain('--pr must be a positive integer');
    }
  });

  it('uses gh pr comment with a generated body-file only in comment mode', () => {
    const outputRoot = makeTempRoot('pr-review-surface-post-comment');
    const bodyFile = join(outputRoot, 'assurance-review.md');
    const fakeGh = join(outputRoot, 'fake-gh.mjs');
    const recordFile = join(outputRoot, 'gh-record.json');
    writeFileSync(bodyFile, '# PR Assurance Review Surface\n\nReview evidence.\n', 'utf8');
    writeFileSync(fakeGh, `#!/usr/bin/env node
import fs from 'node:fs';
const args = process.argv.slice(2);
const bodyFileIndex = args.indexOf('--body-file');
const bodyFile = bodyFileIndex >= 0 ? args[bodyFileIndex + 1] : null;
fs.writeFileSync(${JSON.stringify(recordFile)}, JSON.stringify({
  args,
  bodyFile,
  body: bodyFile ? fs.readFileSync(bodyFile, 'utf8') : null,
}, null, 2));
console.log('https://github.com/example/repo/pull/42#issuecomment-1');
`, 'utf8');
    chmodSync(fakeGh, 0o755);

    const result = runScript([
      '--repo', 'example/repo',
      '--pr', '42',
      '--body-file', bodyFile,
      '--mode', 'comment',
      '--marker', '<!-- custom-marker -->',
      '--gh-bin', fakeGh,
    ]);

    expect(result.status, result.stderr || result.stdout).toBe(0);
    expect(result.stdout).toContain('[assurance-review-surface-post] posted');
    expect(result.stdout).toContain('https://github.com/example/repo/pull/42#issuecomment-1');

    const record = JSON.parse(readFileSync(recordFile, 'utf8'));
    expect(record.args).toEqual([
      'pr',
      'comment',
      '42',
      '--repo',
      'example/repo',
      '--body-file',
      record.bodyFile,
    ]);
    expect(record.body).toContain('<!-- custom-marker -->');
    expect(record.body).toContain('# PR Assurance Review Surface');
    expect(existsSync(record.bodyFile)).toBe(false);
    expect(readFileSync(bodyFile, 'utf8')).toBe('# PR Assurance Review Surface\n\nReview evidence.\n');
  });

  it('returns an actionable authentication error when gh pr comment fails', () => {
    const outputRoot = makeTempRoot('pr-review-surface-post-gh-failure');
    const bodyFile = join(outputRoot, 'assurance-review.md');
    const fakeGh = join(outputRoot, 'fake-gh-fail.mjs');
    writeFileSync(bodyFile, '# Review\n', 'utf8');
    writeFileSync(fakeGh, `#!/usr/bin/env node
console.error('gh: authentication required');
process.exit(1);
`, 'utf8');
    chmodSync(fakeGh, 0o755);

    const result = runScript([
      '--repo', 'example/repo',
      '--pr', '42',
      '--body-file', bodyFile,
      '--mode', 'comment',
      '--gh-bin', fakeGh,
    ]);

    expect(result.status).toBe(1);
    expect(result.stderr).toContain('gh pr comment failed');
    expect(result.stderr).toContain('gh auth login');
    expect(result.stderr).toContain('GH_TOKEN');
    expect(result.stderr).toContain('authentication required');
  });
});
