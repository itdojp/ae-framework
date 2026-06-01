import * as fs from 'node:fs/promises';
import * as path from 'node:path';
import { afterEach, beforeEach, describe, expect, it } from 'vitest';
import {
  BuildVerificationImageArgsSchema,
  CleanupArgsSchema,
  RunContainerVerificationArgsSchema,
} from '../../../src/mcp-server/schemas.js';
import {
  AE_CONTAINER_LABEL_FILTER,
  CONTAINER_CLEANUP_CONFIRM,
  CONTAINER_FORCE_CLEANUP_CONFIRM,
  CONTAINER_PUSH_APPROVAL,
  assertCleanupConfirmation,
  assertPushPolicy,
  redactBuildArgsInMessage,
  redactImageBuildContext,
  resolveApprovedWorkspacePath,
  validateBuildArgs,
  validateContainerTools,
  validateContainerToolsForLanguage,
  validateImageReference,
} from '../../../src/services/container/container-security-policy.js';

const sandboxParent = path.resolve(process.cwd(), '.codex-local/tmp');
let sandboxRoot = '';

describe('container security policy', () => {
  beforeEach(async () => {
    await fs.mkdir(sandboxParent, { recursive: true });
    sandboxRoot = await fs.mkdtemp(path.join(sandboxParent, 'container-security-policy-test-'));
  });

  afterEach(async () => {
    if (sandboxRoot) {
      await fs.rm(sandboxRoot, { recursive: true, force: true });
      sandboxRoot = '';
    }
  });

  it('accepts safe image references and rejects shell-shaped references', () => {
    expect(validateImageReference('ae-framework/verify-rust:latest')).toMatchObject({
      reference: 'ae-framework/verify-rust:latest',
      name: 'ae-framework/verify-rust',
      tag: 'latest',
    });
    expect(validateImageReference('localhost:5000/ae-framework/verify-rust:v1')).toMatchObject({
      registry: 'localhost:5000',
      tag: 'v1',
    });

    expect(() => validateImageReference('ae-framework/verify-rust')).toThrow(/explicit tag/);
    expect(() => validateImageReference('ae-framework/verify-rust:latest;id')).toThrow(/unsupported characters/);
    expect(() => validateImageReference('AE/verify:latest')).toThrow(/Invalid image repository/);
  });



  it('applies the same validation at the Container MCP argument boundary', () => {
    expect(RunContainerVerificationArgsSchema.parse({
      projectPath: 'project',
      language: 'rust',
      tools: ['cargo'],
    }).tools).toEqual(['cargo']);
    expect(() => RunContainerVerificationArgsSchema.parse({
      projectPath: 'project',
      language: 'rust',
      tools: ['cargo;id'],
    })).toThrow(/tool names/);

    expect(BuildVerificationImageArgsSchema.parse({
      language: 'rust',
      tools: ['cargo'],
      buildArgs: { SAFE_KEY: 'value' },
    })).toMatchObject({ push: false, pushApproval: 'none' });
    expect(() => BuildVerificationImageArgsSchema.parse({
      language: 'rust',
      tools: ['cargo'],
      buildArgs: { SAFE_KEY: 'line1\nline2' },
    })).toThrow(/URL\/version-safe/);

    expect(CleanupArgsSchema.parse({})).toMatchObject({ dryRun: true, force: false });
  });

  it('validates verification tools and build arguments before they reach container engines', () => {    expect(validateContainerTools(['cargo', 'miri', 'tool+extra@1'])).toEqual(['cargo', 'miri', 'tool+extra@1']);
    expect(validateContainerToolsForLanguage('rust', ['cargo', 'miri'])).toEqual(['cargo', 'miri']);
    expect(() => validateContainerTools(['cargo;id'])).toThrow(/Invalid verification tool/);
    expect(() => validateContainerToolsForLanguage('elixir', ['cargo'])).toThrow(/Unsupported verification tools/);

    expect(validateBuildArgs({ FEATURE_FLAG: 'enabled', cache_bust: 'https://example.test/v1,abc=123' })).toEqual({
      FEATURE_FLAG: 'enabled',
      cache_bust: 'https://example.test/v1,abc=123',
    });
    expect(() => validateBuildArgs({ 'BAD-KEY': 'value' })).toThrow(/Invalid build argument key/);
    expect(() => validateBuildArgs({ SAFE_KEY: 'line1\nline2' })).toThrow(/Invalid build argument value/);
    expect(() => validateBuildArgs({ SAFE_KEY: 'value with spaces' })).toThrow(/Invalid build argument value/);
  });

  it('requires both per-request approval and configured push prefixes before image push', () => {
    const imageRef = validateImageReference('ghcr.io/example/ae-framework/verify-rust:v1');
    expect(() => assertPushPolicy({ imageRef, push: true })).toThrow(/pushApproval/);
    expect(() => assertPushPolicy({ imageRef, push: true, pushApproval: CONTAINER_PUSH_APPROVAL })).toThrow(/disabled/);
    expect(() => assertPushPolicy({
      imageRef,
      push: true,
      pushApproval: CONTAINER_PUSH_APPROVAL,
      policy: { allowedPushPrefixes: ['ghcr.io/other/'] },
    })).toThrow(/not allowed/);

    expect(() => assertPushPolicy({
      imageRef,
      push: true,
      pushApproval: CONTAINER_PUSH_APPROVAL,
      policy: { allowedPushPrefixes: ['ghcr.io/example/ae-framework/'] },
    })).not.toThrow();

    expect(() => assertPushPolicy({
      imageRef,
      push: true,
      pushApproval: CONTAINER_PUSH_APPROVAL,
      policy: { allowedPushPrefixes: ['ghcr.io/example/ae-framework'] },
    })).not.toThrow();
    expect(() => assertPushPolicy({
      imageRef: validateImageReference('ghcr.io/example/ae-framework:v1'),
      push: true,
      pushApproval: CONTAINER_PUSH_APPROVAL,
      policy: { allowedPushPrefixes: ['ghcr.io/example/ae-framework'] },
    })).not.toThrow();
    expect(() => assertPushPolicy({
      imageRef: validateImageReference('ghcr.io/example/ae-framework-evil:v1'),
      push: true,
      pushApproval: CONTAINER_PUSH_APPROVAL,
      policy: { allowedPushPrefixes: ['ghcr.io/example/ae-framework'] },
    })).toThrow(/not allowed/);
    expect(() => assertPushPolicy({
      imageRef: validateImageReference('ghcr.io/example/ae-framework:release-2026'),
      push: true,
      pushApproval: CONTAINER_PUSH_APPROVAL,
      policy: { allowedPushPrefixes: ['ghcr.io/example/ae-framework:release'] },
    })).not.toThrow();
    expect(() => assertPushPolicy({
      imageRef: validateImageReference('ghcr.io/example/ae-framework:releasecandidate'),
      push: true,
      pushApproval: CONTAINER_PUSH_APPROVAL,
      policy: { allowedPushPrefixes: ['ghcr.io/example/ae-framework:release'] },
    })).toThrow(/not allowed/);
    expect(() => assertPushPolicy({
      imageRef,
      push: true,
      pushApproval: CONTAINER_PUSH_APPROVAL,
      policy: { allowedPushPrefixes: ['ghcr.io/example/ae-framework;id'] },
    })).toThrow(/unsupported characters/);
  });

  it('defaults cleanup to dry-run and requires destructive confirmation tokens', () => {
    expect(AE_CONTAINER_LABEL_FILTER).toBe('label=ae-framework.managed=true');
    expect(assertCleanupConfirmation()).toEqual({ dryRun: true });
    expect(assertCleanupConfirmation({ dryRun: true, force: true })).toEqual({ dryRun: true });
    expect(() => assertCleanupConfirmation({ dryRun: false })).toThrow(CONTAINER_CLEANUP_CONFIRM);
    expect(() => assertCleanupConfirmation({ dryRun: false, force: true, confirm: CONTAINER_CLEANUP_CONFIRM })).toThrow(CONTAINER_FORCE_CLEANUP_CONFIRM);
    expect(assertCleanupConfirmation({ dryRun: false, confirm: CONTAINER_CLEANUP_CONFIRM })).toEqual({ dryRun: false });
    expect(assertCleanupConfirmation({ dryRun: false, force: true, confirm: CONTAINER_FORCE_CLEANUP_CONFIRM })).toEqual({ dryRun: false });
  });

  it('resolves project paths under the approved workspace and rejects symlink escapes', async () => {
    const workspace = path.join(sandboxRoot, 'workspace');
    const project = path.join(workspace, 'project');
    const outside = path.join(sandboxRoot, 'outside');
    await fs.mkdir(project, { recursive: true });
    await fs.mkdir(outside, { recursive: true });
    await fs.symlink(outside, path.join(workspace, 'escape'), process.platform === 'win32' ? 'junction' : 'dir');

    await expect(resolveApprovedWorkspacePath({ workspaceRoot: workspace, projectPath: 'project' }))
      .resolves.toMatchObject({ projectPath: await fs.realpath(project) });
    await expect(resolveApprovedWorkspacePath({ workspaceRoot: workspace, projectPath: path.join(workspace, 'escape') }))
      .rejects.toThrow(/^Project path is outside approved workspace root$/);
    await expect(resolveApprovedWorkspacePath({ workspaceRoot: workspace, projectPath: path.join(workspace, 'missing') }))
      .rejects.toThrow(/^Project path does not exist$/);
  });

  it('redacts build argument values before build contexts and error messages are emitted or logged', () => {
    expect(redactImageBuildContext({
      contextPath: 'containers',
      buildArgs: { TOKEN: 'secret', VERIFICATION_TOOLS: 'cargo' },
    })).toMatchObject({
      buildArgs: { TOKEN: '<redacted>', VERIFICATION_TOOLS: '<redacted>' },
    });
    expect(redactBuildArgsInMessage('docker build --build-arg TOKEN=secret --build-arg VERIFICATION_TOOLS=cargo'))
      .toBe('docker build --build-arg <redacted> --build-arg <redacted>');
  });
});
