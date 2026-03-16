import { mkdtempSync, mkdirSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';

import { describe, expect, it } from 'vitest';

import { resolveDiscoveryToolPaths } from '../../../src/cli/discovery-cli.js';

describe('resolveDiscoveryToolPaths', () => {
  it('resolves the package root from a dist-like module directory', () => {
    const root = mkdtempSync(join(tmpdir(), 'ae-discovery-cli-root-'));
    try {
      const moduleDir = join(root, 'dist', 'src', 'cli');
      const cwd = join(root, 'examples', 'nested');
      mkdirSync(moduleDir, { recursive: true });
      mkdirSync(cwd, { recursive: true });
      mkdirSync(join(root, 'scripts', 'discovery-pack'), { recursive: true });
      mkdirSync(join(root, 'schema'), { recursive: true });
      writeFileSync(join(root, 'package.json'), '{}\n', 'utf8');
      writeFileSync(join(root, 'scripts', 'discovery-pack', 'validate.mjs'), 'export {};\n', 'utf8');
      writeFileSync(join(root, 'scripts', 'discovery-pack', 'compile.mjs'), 'export {};\n', 'utf8');
      writeFileSync(join(root, 'schema', 'discovery-pack-v1.schema.json'), '{}\n', 'utf8');

      expect(resolveDiscoveryToolPaths(cwd, moduleDir)).toEqual({
        repoRoot: root,
        discoveryValidateScript: join(root, 'scripts', 'discovery-pack', 'validate.mjs'),
        discoveryCompileScript: join(root, 'scripts', 'discovery-pack', 'compile.mjs'),
        discoverySchemaPath: join(root, 'schema', 'discovery-pack-v1.schema.json'),
      });
    } finally {
      rmSync(root, { recursive: true, force: true });
    }
  });
});
