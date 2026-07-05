import { mkdirSync, readFileSync, rmSync, writeFileSync, existsSync } from 'node:fs';
import path from 'node:path';
import { describe, expect, it } from 'vitest';
import { scaffoldAssuranceInit } from '../../src/cli/init-cli.js';

const repoRoot = process.cwd();
const tmpRoot = path.join(repoRoot, '.codex-local', 'tmp', 'init-cli-tests');

function resetRoot(name: string): string {
  const root = path.join(tmpRoot, name);
  rmSync(root, { recursive: true, force: true });
  mkdirSync(root, { recursive: true });
  return root;
}

describe('ae init --profile scaffold', () => {
  it('writes the assurance workflow and .ae config for a minimal profile', () => {
    const root = resetRoot('minimal');
    const result = scaffoldAssuranceInit({
      root,
      profile: 'minimal',
      artifactsDir: 'artifacts',
      actionRef: 'v1',
    });

    expect(result.files.map((file) => path.relative(root, file.path)).sort()).toEqual([
      '.ae/assurance.yml',
      '.github/workflows/assurance.yml',
    ]);
    const workflow = readFileSync(path.join(root, '.github/workflows/assurance.yml'), 'utf8');
    expect(workflow).toContain('uses: actions/setup-node@v4');
    expect(workflow).toContain('node-version: "20"');
    expect(workflow).toContain('actions: read');
    expect(workflow).toContain('uses: itdojp/ae-framework@v1');
    expect(workflow).toContain('profile: "minimal"');
    expect(workflow).toContain('artifacts-dir: "artifacts"');
    const config = readFileSync(path.join(root, '.ae/assurance.yml'), 'utf8');
    expect(config).toContain('schemaVersion: ae-assurance-init/v1');
    expect(config).toContain('profileKind: "builtin"');
    expect(config).toContain('action: "itdojp/ae-framework@v1"');
  });

  it('supports dry-run without writing files', () => {
    const root = resetRoot('dry-run');
    const result = scaffoldAssuranceInit({ root, profile: 'standard', dryRun: true });

    expect(result.dryRun).toBe(true);
    expect(existsSync(path.join(root, '.github/workflows/assurance.yml'))).toBe(false);
    expect(result.files[0]?.content).toContain('profile: "standard"');
  });

  it('refuses to overwrite existing files unless force is set', () => {
    const root = resetRoot('overwrite');
    mkdirSync(path.join(root, '.github/workflows'), { recursive: true });
    writeFileSync(path.join(root, '.github/workflows/assurance.yml'), 'existing');

    expect(() => scaffoldAssuranceInit({ root })).toThrow(/refusing to overwrite/);
    expect(() => scaffoldAssuranceInit({ root, force: true })).not.toThrow();
  });

  it('marks custom profile paths as custom in config', () => {
    const root = resetRoot('custom');
    scaffoldAssuranceInit({
      root,
      profile: '.ae/custom-profile.yaml',
      policy: '.ae/policy.yml',
    });

    const config = readFileSync(path.join(root, '.ae/assurance.yml'), 'utf8');
    expect(config).toContain('profileKind: "custom"');
    expect(config).toContain('policy: ".ae/policy.yml"');
  });
});
