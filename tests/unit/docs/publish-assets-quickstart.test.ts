import { existsSync, readFileSync } from 'node:fs';
import path from 'node:path';
import { describe, expect, it } from 'vitest';

const repoRoot = process.cwd();

function readRepoFile(relativePath: string): string {
  return readFileSync(path.join(repoRoot, relativePath), 'utf8');
}

describe('deploy-time profile publish assets', () => {
  it('prepares npm metadata for the standalone core package', () => {
    const packageJson = JSON.parse(readRepoFile('packages/core/package.json'));

    expect(packageJson.name).toBe('@ae-framework/core');
    expect(packageJson.version).toBe('0.1.0');
    expect(packageJson.license).toBe('Apache-2.0');
    expect(packageJson.publishConfig).toMatchObject({ access: 'public' });
    expect(packageJson.repository).toMatchObject({
      type: 'git',
      url: 'git+https://github.com/itdojp/ae-framework.git',
      directory: 'packages/core',
    });
    expect(packageJson.files).toEqual(expect.arrayContaining([
      'dist',
      'schema',
      'README.md',
      'PUBLISHING.md',
    ]));
    expect(Object.keys(packageJson.dependencies).sort()).toEqual(['ajv', 'ajv-formats', 'yaml']);
    expect(packageJson.keywords).toEqual(expect.arrayContaining([
      'assurance',
      'policy-gate',
      'github-actions',
      'json-schema',
    ]));

    const publishing = readRepoFile('packages/core/PUBLISHING.md');
    expect(publishing).toContain('Package metadata is prepared for `@ae-framework/core@0.1.0`');
    expect(publishing).toContain('Publication is not implied by this repository file');
  });

  it('prepares Marketplace metadata and compatibility links for the composite action', () => {
    const action = readRepoFile('.github/actions/assurance-gate/action.yml');
    const actionReadme = readRepoFile('.github/actions/assurance-gate/README.md');

    expect(action).toContain('name: ae-framework Assurance Gate');
    expect(action).toContain('description: Validate assurance artifacts, evaluate a deploy-time profile policy, and render a PR review surface.');
    expect(action).toContain('branding:\n  icon: shield\n  color: blue');
    expect(action).toContain('gate-result:');
    expect(actionReadme).toContain('Marketplace listing metadata draft');
    expect(actionReadme).toContain('docs/getting-started/QUICKSTART-15MIN.md');
    expect(actionReadme).toContain('docs/reference/DEPLOY-TIME-PROFILE-COMPATIBILITY.md');
    expect(actionReadme).toContain('Marketplace publication is not complete');
  });

  it('documents the one-workflow-file quickstart and supported publication boundary', () => {
    const quickstartPath = path.join(repoRoot, 'docs/getting-started/QUICKSTART-15MIN.md');
    expect(existsSync(quickstartPath)).toBe(true);

    const quickstart = readRepoFile('docs/getting-started/QUICKSTART-15MIN.md');
    expect(quickstart).toContain('one workflow file');
    expect(quickstart).toContain('uses: itdojp/ae-framework/.github/actions/assurance-gate@main');
    expect(quickstart).toContain('replace it with `@v1`');
    expect(quickstart).toContain('`mode`: `pass`');
    expect(quickstart).toContain('`mode`: `block`');
    expect(quickstart).toContain('"policyResult": "pass"');
    expect(quickstart).toContain('"policyResult": "block"');
    expect(quickstart).toContain('Do not describe the npm package or Marketplace listing as live');

    const readme = readRepoFile('README.md');
    const docsReadme = readRepoFile('docs/README.md');
    expect(readme).toContain('docs/getting-started/QUICKSTART-15MIN.md');
    expect(docsReadme).toContain('getting-started/QUICKSTART-15MIN.md');
  });

  it('records action, profile, schema, and core compatibility rules', () => {
    const compatibility = readRepoFile('docs/reference/DEPLOY-TIME-PROFILE-COMPATIBILITY.md');

    expect(compatibility).toContain('@ae-framework/core` `0.1.0`');
    expect(compatibility).toContain('ref is the compatibility anchor');
    expect(compatibility).toContain('schemaVersion: assurance-profile/v1');
    expect(compatibility).toContain('schemaVersion: ae-release-policy/v1');
    expect(compatibility).toContain('Use a commit SHA or `main` for preview validation; use `v1` only after the release tag is cut.');
    expect(compatibility).toContain('tests/actions/assurance-gate-action.test.ts');
  });

  it('keeps release and announcement copy separated from unexecuted publication claims', () => {
    const releaseAssets = readRepoFile('docs/product/DEPLOY-TIME-PROFILE-PUBLISH-ASSETS-2026-07-04.md');

    expect(releaseAssets).toContain('npm publication is not claimed');
    expect(releaseAssets).toContain('Marketplace publication is not claimed');
    expect(releaseAssets).toContain('Unsupported until release execution');
    expect(releaseAssets).toContain('external adoption surface');
    expect(releaseAssets).toContain('review-speed improvement');
  });
});
