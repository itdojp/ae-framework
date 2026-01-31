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

    const job = workflow.jobs?.handle_issue_commands;
    expect(job).toBeDefined();

    const ifExpr = String(job.if || '');
    expect(ifExpr).toContain('github.event.issue.pull_request == null');
    expect(ifExpr).toContain("vars.AE_SLASH_COMMANDS_ISSUE == '1'");
  });

  it('limits permissions to read contents + write issues', () => {
    const perms = workflow.permissions || {};
    expect(perms.contents).toBe('read');
    expect(perms.issues).toBe('write');
    const keys = Object.keys(perms);
    expect(keys.sort()).toEqual(['contents', 'issues']);
  });

  it('does not cancel in-flight runs for idempotency', () => {
    expect(workflow.concurrency?.['cancel-in-progress']).toBe(false);
  });
});
