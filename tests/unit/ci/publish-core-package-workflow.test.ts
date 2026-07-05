import fs from 'node:fs';
import path from 'node:path';
import { describe, expect, it } from 'vitest';
import yaml from 'js-yaml';

const repoRoot = process.cwd();
const workflowPath = path.join(repoRoot, '.github/workflows/publish-core-package.yml');

describe('publish core package workflow', () => {
  it('defaults to preflight and gates npm publication behind protected trusted publishing', () => {
    const raw = fs.readFileSync(workflowPath, 'utf8');
    const workflow = yaml.load(raw) as any;
    const dispatch = workflow.on?.workflow_dispatch;
    const bootstrapJob = workflow.jobs?.['bootstrap-publish'];
    const trustedJob = workflow.jobs?.['trusted-publish'];

    expect(workflow.name).toBe('Publish @ae-framework/core');
    expect(workflow.on?.pull_request).toBeUndefined();
    expect(workflow.on?.push).toBeUndefined();
    expect(dispatch?.inputs?.publish_mode?.default).toBe('preflight');
    expect(dispatch?.inputs?.publish_mode?.type).toBe('choice');
    expect(dispatch?.inputs?.publish_mode?.options).toEqual([
      'preflight',
      'bootstrap-token',
      'trusted-publisher',
    ]);
    expect(dispatch?.inputs?.package_version?.default).toBe('0.1.0');

    expect(workflow.permissions).toEqual({ contents: 'read' });
    expect(bootstrapJob?.if).toBe("${{ inputs.publish_mode == 'bootstrap-token' }}");
    expect(bootstrapJob?.environment?.name).toBe('npm-publish-bootstrap');
    expect(bootstrapJob?.permissions).toEqual({ contents: 'read', 'id-token': 'write' });
    expect(trustedJob?.if).toBe("${{ inputs.publish_mode == 'trusted-publisher' }}");
    expect(trustedJob?.environment?.name).toBe('npm-publish');
    expect(trustedJob?.permissions).toEqual({ contents: 'read', 'id-token': 'write' });
    expect(raw).toContain("node-version: '22.14.0'");
    expect(raw).toContain("npm install -g 'npm@^11.5.1'");
    expect(raw).toContain('npm provenance publishing requires Node >=22.14.0');
    expect(raw).toContain('npm trusted publishing requires Node >=22.14.0');
    expect(raw).toContain('npm trusted publishing requires npm >=11.5.1');
    expect(raw).toContain('expected_tag="core-v${EXPECTED_VERSION}"');
    expect(raw).toContain('Bootstrap publishing requires dispatching this workflow on tag ${expected_tag}');
    expect(raw).toContain('Trusted publishing requires dispatching this workflow on tag ${expected_tag}');
    expect(raw).toContain('@ae-framework/core does not exist on npm yet. Use publish_mode=bootstrap-token');
    expect(raw).toContain('NODE_AUTH_TOKEN: ${{ secrets.NPM_BOOTSTRAP_TOKEN }}');
    expect(raw).not.toContain('NPM_TOKEN');
  });

  it('runs package preflight checks and publishes with provenance only in the publish job', () => {
    const raw = fs.readFileSync(workflowPath, 'utf8');
    const workflow = yaml.load(raw) as any;
    const preflight = workflow.jobs?.preflight;
    const bootstrapJob = workflow.jobs?.['bootstrap-publish'];
    const trustedJob = workflow.jobs?.['trusted-publish'];

    expect(preflight?.name).toBe('core-package-preflight');
    expect(bootstrapJob?.name).toBe('core-package-bootstrap-publish');
    expect(trustedJob?.name).toBe('core-package-trusted-publish');
    expect(raw).toContain('pnpm --filter @ae-framework/core run build');
    expect(raw).toContain('pnpm --filter @ae-framework/core run test');
    expect(raw).toContain('pnpm --filter @ae-framework/core run check:no-src-imports');
    expect(raw).toContain('npm pack --dry-run --json --foreground-scripts=false > ../../artifacts/npm/core-pack-dry-run.json');
    expect(raw).toContain("for (const required of ['package.json', 'README.md', 'PUBLISHING.md', 'LICENSE', 'NOTICE'])");
    expect(raw).toContain('actions/upload-artifact@v4');
    expect(raw).toContain('Publish initial @ae-framework/core with bootstrap token and provenance');
    expect(raw).toContain('Publish @ae-framework/core with trusted publishing provenance');
    expect(raw.match(/npm publish --provenance --access public/g)).toHaveLength(2);
    expect(raw).toContain('npm view @ae-framework/core version --json');
  });
});
