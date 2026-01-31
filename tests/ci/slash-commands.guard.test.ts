/**
 * Slash commands workflow safety guard.
 * Ensures issue-only triggers, minimal permissions, and idempotent concurrency.
 */
import { describe, it, expect } from 'vitest';
import { readFileSync } from 'fs';
import yaml from 'js-yaml';

interface GitHubWorkflow {
  on?: {
    issue_comment?: {
      types?: string[];
    };
  };
  permissions?: Record<string, string>;
  concurrency?: {
    cancel-in-progress?: boolean;
  };
  jobs?: Record<string, any>;
}

describe('Slash commands workflow safety guard', () => {
  const workflowPath = '.github/workflows/slash-commands.yml';
  const workflow = yaml.load(readFileSync(workflowPath, 'utf8')) as GitHubWorkflow;

  it('is issue-comment only and gated for non-PR issues', () => {
    expect(workflow.on?.issue_comment?.types).toContain('created');

    const onConfig = ((workflow as any).on ?? {}) as Record<string, unknown>;
    const onKeys = Object.keys(onConfig);
    const disallowedEvents = ['pull_request_comment', 'pull_request_target', 'workflow_dispatch', 'pull_request'];
    for (const event of disallowedEvents) {
      expect(onKeys).not.toContain(event);
    }

    const job = workflow.jobs?.handle_issue_commands;
    expect(job).toBeDefined();

    const ifExpr = String(job.if || '');
    expect(ifExpr).toMatch(
      /github\.event\.issue\.pull_request\s*==\s*null\s*&&\s*vars\.AE_SLASH_COMMANDS_ISSUE\s*==\s*'1'/
    );
  });

  it('limits permissions to read contents + write issues', () => {
    const perms = workflow.permissions || {};
    expect(perms.contents).toBe('read');
    expect(perms.issues).toBe('write');
    const keys = Object.keys(perms);
    expect(keys.sort()).toEqual(['contents', 'issues']);
    expect(perms['id-token']).toBeUndefined();
    expect(perms['pull-requests']).toBeUndefined();
    expect(perms.packages).toBeUndefined();

    const jobPerms = workflow.jobs?.handle_issue_commands?.permissions;
    if (jobPerms) {
      expect(jobPerms.contents).toBe('read');
      expect(jobPerms.issues).toBe('write');
      expect(Object.keys(jobPerms).sort()).toEqual(['contents', 'issues']);
    }
  });

  it('does not cancel in-flight runs for idempotency', () => {
    expect(workflow.concurrency?.['cancel-in-progress']).toBe(false);
  });
});
