import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';

import { afterEach, describe, expect, it, vi } from 'vitest';

import type { TaskRequest } from '../../../src/agents/task-types';
import {
  collectRequestedSources,
  extractValidationInput,
  formatSourceSummary,
  resolveValidationSources,
  toValidationInput,
} from '../../../src/agents/validation-task-input';

function createRequest(overrides: Partial<TaskRequest> = {}): TaskRequest {
  return {
    description: 'validation',
    prompt: '',
    subagent_type: 'validation',
    ...overrides,
  };
}

function createTempDir(): string {
  return fs.mkdtempSync(path.join(os.tmpdir(), 'validation-task-input-'));
}

function removeTempDir(dir: string): void {
  fs.rmSync(dir, { recursive: true, force: true });
}

describe('validation-task-input', () => {
  const tempDirs: string[] = [];

  afterEach(() => {
    while (tempDirs.length > 0) {
      const dir = tempDirs.pop();
      if (!dir) {
        continue;
      }
      removeTempDir(dir);
    }
  });

  it('collectRequestedSources prioritizes context.sources array', () => {
    const request = createRequest({
      context: {
        sources: [' docs/req.md ', '', 123, 'specs/api.md'],
      },
      prompt: 'ignored.md',
    });

    expect(collectRequestedSources(request)).toEqual(['docs/req.md', 'specs/api.md']);
  });

  it('extractValidationInput resolves files and directories with stable ordering', () => {
    const root = createTempDir();
    tempDirs.push(root);
    const docsDir = path.join(root, 'docs');
    fs.mkdirSync(docsDir);
    fs.writeFileSync(path.join(docsDir, 'b.md'), '# B');
    fs.writeFileSync(path.join(docsDir, 'a.md'), '# A');
    fs.writeFileSync(path.join(docsDir, 'ignore.png'), 'bin');

    const request = createRequest({
      context: {
        sources: ['docs'],
      },
    });

    const input = extractValidationInput(request, { cwd: root });

    expect(input.requestedSources).toEqual(['docs']);
    expect(input.missingSources).toEqual([]);
    expect(input.resolvedSources.map((item) => item.path)).toEqual(['docs/a.md', 'docs/b.md']);
    expect(formatSourceSummary(input)).toContain('Resolved: 2');
  });

  it('resolveValidationSources keeps inline source and marks missing path', () => {
    const root = createTempDir();
    tempDirs.push(root);

    const resolved = resolveValidationSources(['inline requirement text', 'missing-file.md'], { cwd: root });

    expect(resolved.resolvedSources).toHaveLength(1);
    expect(resolved.resolvedSources[0]?.path).toContain('inline:');
    expect(resolved.missingSources).toEqual(['missing-file.md']);
  });

  it('extractValidationInput throws when all requested sources are unreadable', () => {
    const request = createRequest({
      context: {
        sources: ['missing-file.md'],
      },
    });

    expect(() => extractValidationInput(request, { cwd: os.tmpdir() })).toThrow(
      'No readable validation sources found',
    );
  });

  it('toValidationInput filters invalid entries and keeps strict flag', () => {
    const warnSpy = vi.spyOn(console, 'warn').mockImplementation(() => {});
    const normalized = toValidationInput({
      requestedSources: ['valid.md', 42],
      resolvedSources: [{ path: 'valid.md', content: 'ok' }, { path: '', content: 'invalid' }],
      missingSources: ['missing.md', {}],
      strict: 1,
    });
    warnSpy.mockRestore();

    expect(normalized).toEqual({
      requestedSources: ['valid.md'],
      resolvedSources: [{ path: 'valid.md', content: 'ok' }],
      missingSources: ['missing.md'],
      strict: true,
    });
  });
});
