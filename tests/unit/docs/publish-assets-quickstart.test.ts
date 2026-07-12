import { existsSync, readFileSync } from 'node:fs';
import path from 'node:path';
import { describe, expect, it } from 'vitest';
import YAML from 'yaml';

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
      'LICENSE',
      'NOTICE',
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
    expect(publishing).toContain('package-local `LICENSE` and `NOTICE` files');
  });

  it('prepares Marketplace metadata and compatibility links for the composite action', () => {
    const action = readRepoFile('action.yml');
    const subdirectoryAction = readRepoFile('.github/actions/assurance-gate/action.yml');
    const actionReadme = readRepoFile('.github/actions/assurance-gate/README.md');
    const rootMetadata = YAML.parse(action);
    const subdirectoryMetadata = YAML.parse(subdirectoryAction);

    expect(action).toContain('name: ae-framework Assurance Gate');
    expect(action).toContain('description: Validate assurance artifacts, evaluate a deploy-time profile policy, and render a PR review surface.');
    expect(action).toContain('branding:\n  icon: shield\n  color: blue');
    expect(action).toContain('gate-result:');
    expect(action).toContain('node "${GITHUB_ACTION_PATH}/scripts/actions/assurance-gate.mjs"');
    expect(subdirectoryAction).toContain('node "${GITHUB_ACTION_PATH}/../../../scripts/actions/assurance-gate.mjs"');
    expect(rootMetadata.name).toBe(subdirectoryMetadata.name);
    expect(rootMetadata.description).toBe(subdirectoryMetadata.description);
    expect(rootMetadata.branding).toEqual(subdirectoryMetadata.branding);
    expect(Object.keys(rootMetadata.inputs).sort()).toEqual(Object.keys(subdirectoryMetadata.inputs).sort());
    expect(Object.keys(rootMetadata.outputs).sort()).toEqual(Object.keys(subdirectoryMetadata.outputs).sort());
    expect(actionReadme).toContain('Marketplace listing metadata draft');
    expect(actionReadme).toContain('docs/getting-started/QUICKSTART-15MIN.md');
    expect(actionReadme).toContain('docs/reference/DEPLOY-TIME-PROFILE-COMPATIBILITY.md');
    expect(actionReadme).toContain('Marketplace publication is still not complete');
    expect(actionReadme).toContain('root action');
  });

  it('documents the one-workflow-file quickstart and supported publication boundary', () => {
    const quickstartPath = path.join(repoRoot, 'docs/getting-started/QUICKSTART-15MIN.md');
    expect(existsSync(quickstartPath)).toBe(true);

    const quickstart = readRepoFile('docs/getting-started/QUICKSTART-15MIN.md');
    expect(quickstart).toContain('one workflow file');
    expect(quickstart).toContain('actions: read');
    expect(quickstart).toContain('uses: itdojp/ae-framework@v1');
    expect(quickstart).toContain('replace `@v1` with `@v1.0.2`');
    expect(quickstart).toContain('`mode`: `pass`');
    expect(quickstart).toContain('`mode`: `block`');
    expect(quickstart).toContain('"policyResult": "pass"');
    expect(quickstart).toContain('"policyResult": "block"');
    expect(quickstart).toContain('Do not describe the npm package or Marketplace');
    expect(quickstart).toContain('listing as live unless the release note for that publication exists');
    expect(quickstart).toContain('successful path-resolution check is not');

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
    expect(compatibility).toContain('Use `v1` for normal adoption after the release tag exists; use `v1.0.2` or a commit SHA for reproducibility.');
    expect(compatibility).toContain('--config.use-lockfile=true --config.package-lock=true');
    expect(compatibility).toContain('historical `v1.0.1` tag remains immutable');
    expect(compatibility).toContain('tests/actions/assurance-gate-action.test.ts');
  });

  it('keeps release and announcement copy separated from unexecuted publication claims', () => {
    const releaseAssets = readRepoFile('docs/product/DEPLOY-TIME-PROFILE-PUBLISH-ASSETS-2026-07-04.md');

    expect(releaseAssets).toContain('npm publication is not claimed');
    expect(releaseAssets).toContain('Marketplace publication is not claimed');
    expect(releaseAssets).toContain('listing URL is recorded');
    expect(releaseAssets).toContain('Unsupported until release execution');
    expect(releaseAssets).toContain('external adoption surface');
    expect(releaseAssets).toContain('review-speed improvement');
  });

  it('documents the root action release tag policy', () => {
    const releasePolicy = readRepoFile('docs/operate/ASSURANCE-GATE-ACTION-RELEASE.md');

    expect(releasePolicy).toContain('`action.yml` at repository root');
    expect(releasePolicy).toContain('`v1.0.1`');
    expect(releasePolicy).toContain('`v1.0.2`');
    expect(releasePolicy).toContain('historical bootstrap tag');
    expect(releasePolicy).toContain('`v1`');
    expect(releasePolicy).toContain('git tag -a v1.0.2');
    expect(releasePolicy).toContain('export CANDIDATE_SHA as the reviewed-and-smoked 40-character merge commit');
    expect(releasePolicy).toContain('test "$RELEASE_SHA" = "$CANDIDATE_SHA"');
    expect(releasePolicy).toContain('gh release create v1.0.2');
    expect(releasePolicy).toContain('--notes-file docs/operate/ASSURANCE-GATE-V1.0.2-RELEASE-NOTES.md');
    expect(releasePolicy).not.toContain('git push origin refs/tags/v1 --force');
    expect(releasePolicy).toContain('--force-with-lease="refs/tags/v1:${PREVIOUS_V1_OBJECT}"');
    expect(releasePolicy).toContain('git ls-remote --refs --tags origin refs/tags/v1');
    expect(releasePolicy).toContain('PREVIOUS_V1_COMMIT');
    expect(releasePolicy).toContain('FAILED_V1_OBJECT');
    expect(releasePolicy).toContain('External runtime smoke sequence');
    expect(releasePolicy).toContain('itdojp/ae-framework-impl-test-hub');
    expect(releasePolicy).toContain('fail-on-block=false');
    expect(releasePolicy).toContain('resolved-commit parity');

    const releaseNotes = readRepoFile('docs/operate/ASSURANCE-GATE-V1.0.2-RELEASE-NOTES.md');
    expect(releaseNotes).toContain('ERR_PNPM_LOCKFILE_CONFIG_MISMATCH');
    expect(releaseNotes).toContain('Before creating the immutable tag');
    expect(releaseNotes).toContain('After the GitHub Release exists');
    expect(releaseNotes).toContain('does not by itself publish');
    expect(releaseNotes).toContain('Do not rewrite or delete `v1.0.2`');
  });
});
