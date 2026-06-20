import {
  mkdirSync,
  mkdtempSync,
  readFileSync,
  rmSync,
  statSync,
  symlinkSync,
  writeFileSync,
} from 'node:fs';
import { join } from 'node:path';
import { describe, expect, it } from 'vitest';
import {
  commandExamples,
  formatTaskMarkdown,
  parseArgs,
  resolveOutputPath,
  run,
} from '../../../scripts/codex/export-issue-task.mjs';

function writeFakeGh(tempDir: string, payload: { title: string; url: string; body: string }) {
  if (process.platform === 'win32') {
    const fixturePath = join(tempDir, 'gh-fixture.mjs');
    writeFileSync(fixturePath, `console.log(${JSON.stringify(JSON.stringify(payload))});\n`);
    const ghPath = join(tempDir, 'gh.cmd');
    writeFileSync(ghPath, `@echo off\r\n"${process.execPath}" "${fixturePath}" %*\r\n`);
    return ghPath;
  }

  const ghPath = join(tempDir, 'gh');
  writeFileSync(
    ghPath,
    [
      '#!/usr/bin/env node',
      `console.log(${JSON.stringify(JSON.stringify(payload))});`,
    ].join('\n'),
    { mode: 0o755 },
  );
  return ghPath;
}

describe('codex issue task exporter', () => {
  it('formats a task file with source URL, metadata, and Context Pack preflight', () => {
    const markdown = formatTaskMarkdown({
      issue: 3490,
      repo: 'itdojp/ae-framework',
      title: '[ACP-050] Codex CLI issue runner',
      url: 'https://github.com/itdojp/ae-framework/issues/3490',
      body: '## Acceptance criteria\n- [ ] task URL remains visible',
      generatedAt: '2026-06-20T00:00:00.000Z',
      includePreflight: true,
    });

    expect(markdown).toContain('# [ACP-050] Codex CLI issue runner');
    expect(markdown).toContain('Issue: https://github.com/itdojp/ae-framework/issues/3490');
    expect(markdown).toContain('Local task file: do not stage or commit this file.');
    expect(markdown).toContain('## Context Pack preflight');
    expect(markdown).toContain('Context Pack conflict: none');
    expect(markdown).toContain('## Issue body');
    expect(markdown).toContain('task URL remains visible');
  });

  it('keeps default output under .codex-local/tasks', () => {
    const { workRoot, outputPath } = resolveOutputPath({
      work: '/repo/worktree',
      out: null,
      issue: 3490,
    });

    expect(workRoot).toBe('/repo/worktree');
    expect(outputPath).toBe('/repo/worktree/.codex-local/tasks/issue-3490.md');
  });

  it('rejects output paths outside the work root', () => {
    expect(() => resolveOutputPath({
      work: '/repo/worktree',
      out: '../issue.md',
      issue: 3490,
    })).toThrow(/output path must stay under work root/);
  });

  it('runs gh issue view and writes the local task file', () => {
    const tempRoot = join(process.cwd(), 'tmp');
    mkdirSync(tempRoot, { recursive: true });
    const tempDir = mkdtempSync(join(tempRoot, 'codex-issue-task-'));
    const ghPath = writeFakeGh(tempDir, {
      title: 'Exported Issue',
      url: 'https://github.com/itdojp/ae-framework/issues/3490',
      body: '## Body\nTask details',
    });

    try {
      const result = run(parseArgs([
        '--issue', '3490',
        '--repo', 'itdojp/ae-framework',
        '--work', tempDir,
        '--gh', ghPath,
        '--generated-at', '2026-06-20T00:00:00.000Z',
      ]));

      expect(result?.outputPath).toBe(join(tempDir, '.codex-local/tasks/issue-3490.md'));
      expect(statSync(result!.outputPath).isFile()).toBe(true);
      const task = readFileSync(result!.outputPath, 'utf8');
      expect(task).toContain('# Exported Issue');
      expect(task).toContain('Issue: https://github.com/itdojp/ae-framework/issues/3490');
      expect(task).toContain('Task details');
    } finally {
      rmSync(tempDir, { recursive: true, force: true });
    }
  });

  it('rejects symlinked output directories that resolve outside the work root', () => {
    const tempRoot = join(process.cwd(), 'tmp');
    mkdirSync(tempRoot, { recursive: true });
    const tempDir = mkdtempSync(join(tempRoot, 'codex-issue-task-'));
    const workRoot = join(tempDir, 'work');
    const outsideRoot = join(tempDir, 'outside');
    mkdirSync(workRoot, { recursive: true });
    mkdirSync(outsideRoot, { recursive: true });
    const ghPath = writeFakeGh(tempDir, {
      title: 'Escaping Issue',
      url: 'https://github.com/itdojp/ae-framework/issues/3490',
      body: 'body',
    });
    try {
      symlinkSync(outsideRoot, join(workRoot, '.codex-local'), 'dir');
    } catch {
      rmSync(tempDir, { recursive: true, force: true });
      return;
    }

    try {
      expect(() => run(parseArgs([
        '--issue', '3490',
        '--repo', 'itdojp/ae-framework',
        '--work', workRoot,
        '--gh', ghPath,
      ]))).toThrow(/after resolving symlinks/);
    } finally {
      rmSync(tempDir, { recursive: true, force: true });
    }
  });

  it('rejects symlink output files even when the target does not exist', () => {
    const tempRoot = join(process.cwd(), 'tmp');
    mkdirSync(tempRoot, { recursive: true });
    const tempDir = mkdtempSync(join(tempRoot, 'codex-issue-task-'));
    const workRoot = join(tempDir, 'work');
    const outsideRoot = join(tempDir, 'outside');
    const taskDir = join(workRoot, '.codex-local', 'tasks');
    const outputPath = join(taskDir, 'issue-3490.md');
    mkdirSync(taskDir, { recursive: true });
    mkdirSync(outsideRoot, { recursive: true });
    const ghPath = writeFakeGh(tempDir, {
      title: 'Broken Symlink Issue',
      url: 'https://github.com/itdojp/ae-framework/issues/3490',
      body: 'body',
    });
    try {
      symlinkSync(join(outsideRoot, 'missing-task.md'), outputPath, 'file');
    } catch {
      rmSync(tempDir, { recursive: true, force: true });
      return;
    }

    try {
      expect(() => run(parseArgs([
        '--issue', '3490',
        '--repo', 'itdojp/ae-framework',
        '--work', workRoot,
        '--gh', ghPath,
      ]))).toThrow(/output file must not be a symbolic link/);
    } finally {
      rmSync(tempDir, { recursive: true, force: true });
    }
  });

  it('prints dedicated worktree and non-interactive Codex command examples', () => {
    const examples = commandExamples({
      issue: 3490,
      workRoot: '/workspace/ae-framework',
      outputPath: '/workspace/ae-framework/.codex-local/tasks/issue-3490.md',
    });

    expect(examples).toContain('git worktree add');
    expect(examples).toContain('ae-framework-3490-work');
    expect(examples).toContain("--cd '/workspace/ae-framework-3490-work'");
    expect(examples).toContain('Preflight reminder');
    expect(examples).toContain('Context Pack conflict: found');
    expect(examples).toContain('--sandbox workspace-write --ask-for-approval never');
  });

  it('keeps the PowerShell helper aligned with the documented export contract', () => {
    const helper = readFileSync('scripts/codex/Export-CodexIssueTask.ps1', 'utf8');

    expect(helper).toContain('gh issue view $Issue --repo $Repo --json title,body,url');
    expect(helper).toContain('Issue must be a positive integer.');
    expect(helper).toContain('.codex-local/tasks/issue-$Issue.md');
    expect(helper).toContain('Assert-ResolvedUnderRoot');
    expect(helper).toContain('Assert-OutputFileIsNotLink');
    expect(helper).toContain('ConvertTo-SingleQuotedArgument');
    expect(helper).toContain('Context Pack preflight');
    expect(helper).toContain('Context Pack conflict: found');
    expect(helper).toContain('Do not stage or commit `.codex-local/tasks/`');
    expect(helper).toContain('Use a dedicated worktree for parallel Issue work.');
    expect(helper).toContain('--sandbox workspace-write --ask-for-approval never');
    expect(helper).toContain('New-Item -ItemType Directory -Force -LiteralPath');
    expect(helper).toContain('Set-Content -LiteralPath');
    expect(helper).toContain('Get-Content -Raw -LiteralPath');
    expect(helper).toContain('codex exec --cd $quotedSibling');
    expect(helper).toContain('[switch]$Help');
  });
});
