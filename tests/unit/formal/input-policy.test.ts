import { describe, expect, it } from 'vitest';
import { mkdirSync, mkdtempSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { tmpdir } from 'node:os';

import {
  resolveRepoRelativeFileInput,
  validateChoice,
} from '../../../scripts/formal/input-policy.mjs';

describe('formal input policy', () => {
  it('accepts approved repository-relative TLA files', () => {
    const root = mkdtempSync(join(tmpdir(), 'formal-input-policy-'));
    mkdirSync(join(root, 'spec', 'tla'), { recursive: true });
    writeFileSync(join(root, 'spec', 'tla', 'DomainSpec.tla'), '---- MODULE DomainSpec ----\n', 'utf8');

    const result = resolveRepoRelativeFileInput('spec/tla/DomainSpec.tla', {
      repoRoot: root,
      defaultPath: 'spec/tla/DomainSpec.tla',
      allowedRoots: ['spec/tla'],
      allowedExtensions: ['.tla'],
      name: 'TLA file',
    });

    expect(result.relativePath).toBe('spec/tla/DomainSpec.tla');
    expect(result.absolutePath).toBe(join(root, 'spec', 'tla', 'DomainSpec.tla'));
  });

  it.each([
    '/etc/passwd',
    'C:\\Windows\\win.ini',
    '../spec/tla/DomainSpec.tla',
    'spec/tla/../../package.json',
    'spec\\tla\\DomainSpec.tla',
    'scripts/formal/verify-tla.mjs',
    'spec/tla/DomainSpec.js',
    'spec/tla/DomainSpec.tla\u0000',
  ])('rejects unsafe formal file input %s', (candidate) => {
    expect(() => resolveRepoRelativeFileInput(candidate, {
      repoRoot: process.cwd(),
      defaultPath: 'spec/tla/DomainSpec.tla',
      allowedRoots: ['spec/tla'],
      allowedExtensions: ['.tla'],
      name: 'TLA file',
    })).toThrow();
  });

  it('validates finite dispatch choices', () => {
    expect(validateChoice('apalache', {
      allowed: ['tlc', 'apalache'],
      name: 'engine',
      defaultValue: 'tlc',
    })).toBe('apalache');

    expect(() => validateChoice('$(echo injected)', {
      allowed: ['tlc', 'apalache'],
      name: 'engine',
      defaultValue: 'tlc',
    })).toThrow('engine must be one of');
  });
});
