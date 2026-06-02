import { afterEach, describe, expect, it } from 'vitest';
import { existsSync, mkdirSync, rmSync, symlinkSync } from 'node:fs';
import { join, relative } from 'node:path';
import { createCodexTaskAdapter } from '../../../src/agents/codex-task-adapter.js';
import type { TaskRequest } from '../../../src/agents/task-types.js';

const artifactRoot = join(process.cwd(), 'artifacts', 'testing');

function makeOutputDir(): { relativeDir: string; absoluteDir: string; cleanup: () => void } {
  mkdirSync(artifactRoot, { recursive: true });
  const relativeDir = `artifacts/testing/codex-ui-security-${process.pid}-${Date.now()}-${Math.random().toString(16).slice(2)}`;
  const absoluteDir = join(process.cwd(), relativeDir);
  return {
    relativeDir,
    absoluteDir,
    cleanup: () => rmSync(absoluteDir, { recursive: true, force: true }),
  };
}

function makePhaseState() {
  return {
    entities: {
      '../../Admin Panel': {
        description: 'Admin panel',
        attributes: {
          id: { type: 'uuid', required: true, description: 'Identifier' },
          name: { type: 'string', required: true, description: 'Name' },
          createdAt: { type: 'date', required: false, description: 'Created timestamp' },
        },
        acceptance_criteria: ['Name is required'],
      },
    },
  };
}

function makeRequest(context: TaskRequest['context']): TaskRequest {
  return {
    description: 'Generate UI scaffold',
    prompt: 'Generate UI scaffold',
    subagent_type: 'ui',
    context,
  };
}

describe('CodeX Task UI scaffold security boundary', () => {
  let cleanup: (() => void) | undefined;

  afterEach(() => {
    cleanup?.();
    cleanup = undefined;
  });

  it('forces untrusted UI scaffold requests to dry-run before filesystem writes', async () => {
    const output = makeOutputDir();
    cleanup = output.cleanup;
    const adapter = createCodexTaskAdapter();

    const response = await adapter.handleTask(makeRequest({
      phaseState: makePhaseState(),
      outputDir: output.relativeDir,
      dryRun: false,
    }));

    expect(response.shouldBlockProgress).toBe(false);
    expect(response.summary).toContain('(dry-run)');
    expect(response.warnings).toEqual(expect.arrayContaining([
      expect.stringContaining('untrusted-ui-request-forced-dry-run'),
    ]));
    expect(existsSync(join(output.absoluteDir, 'apps', 'web', 'app', 'admin-panel', 'page.tsx'))).toBe(false);
  });

  it('blocks absolute and parent-directory UI output roots before scaffolding', async () => {
    const adapter = createCodexTaskAdapter();

    const response = await adapter.handleTask(makeRequest({
      phaseState: makePhaseState(),
      outputDir: '../outside-ui-root',
      dryRun: false,
      approval: { approved: true, scope: 'ui-scaffold' },
    }));

    expect(response.shouldBlockProgress).toBe(true);
    expect(response.blockingReason).toBe('unsafe-ui-output-dir');
    expect(response.warnings).toEqual(expect.arrayContaining([
      expect.stringContaining('context.outputDir must not contain parent-directory'),
    ]));
  });

  it('blocks UI output roots whose existing ancestor resolves outside the repository', async () => {
    mkdirSync(artifactRoot, { recursive: true });
    const outside = join(process.cwd(), '..', `codex-ui-outside-${process.pid}-${Date.now()}-${Math.random().toString(16).slice(2)}`);
    const symlinkPath = join(artifactRoot, `codex-ui-link-${process.pid}-${Date.now()}-${Math.random().toString(16).slice(2)}`);
    mkdirSync(outside, { recursive: true });
    try {
      symlinkSync(outside, symlinkPath, 'dir');
    } catch {
      rmSync(outside, { recursive: true, force: true });
      return;
    }
    cleanup = () => {
      rmSync(symlinkPath, { recursive: true, force: true });
      rmSync(outside, { recursive: true, force: true });
    };
    const adapter = createCodexTaskAdapter();

    const response = await adapter.handleTask(makeRequest({
      phaseState: makePhaseState(),
      outputDir: relative(process.cwd(), symlinkPath),
      dryRun: false,
      approval: { approved: true, scope: 'ui-scaffold' },
    }));

    expect(response.shouldBlockProgress).toBe(true);
    expect(response.blockingReason).toBe('unsafe-ui-output-dir');
    expect(response.warnings).toEqual(expect.arrayContaining([
      expect.stringContaining('symlink outside the repository workspace'),
    ]));
  });

  it('writes only under the approved output root and sanitizes entity path segments for trusted requests', async () => {
    const output = makeOutputDir();
    cleanup = output.cleanup;
    const adapter = createCodexTaskAdapter();

    const response = await adapter.handleTask(makeRequest({
      phaseState: makePhaseState(),
      outputDir: output.relativeDir,
      dryRun: false,
      approval: { approved: true, scope: 'ui-scaffold', actor: 'operator' },
    }));

    expect(response.shouldBlockProgress).toBe(false);
    expect(response.summary).not.toContain('(dry-run)');
    expect(response.analysis).toContain('apps/web/app/admin-panel/page.tsx');
    expect(existsSync(join(output.absoluteDir, 'apps', 'web', 'app', 'admin-panel', 'page.tsx'))).toBe(true);
    expect(existsSync(join(output.absoluteDir, '..', 'Admin Panel', 'page.tsx'))).toBe(false);
  });
});
