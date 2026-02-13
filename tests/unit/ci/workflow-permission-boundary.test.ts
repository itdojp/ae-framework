import fs from 'node:fs';
import path from 'node:path';
import { describe, expect, it } from 'vitest';

const readWorkflow = (name: string) => fs.readFileSync(
  path.resolve(process.cwd(), '.github/workflows', name),
  'utf8',
);

describe('workflow permission boundaries', () => {
  it('copilot-auto-fix blocks fork PRs and supports global kill-switch', () => {
    const workflow = readWorkflow('copilot-auto-fix.yml');
    expect(workflow).toContain('github.event.pull_request.head.repo.fork == false');
    expect(workflow).toContain('AE_AUTOMATION_GLOBAL_DISABLE');
  });

  it('codex-autopilot-lane issue_comment path requires trusted command + association', () => {
    const workflow = readWorkflow('codex-autopilot-lane.yml');
    expect(workflow).toContain("github.event.issue.pull_request");
    expect(workflow).toContain("contains(github.event.comment.body, '/autopilot run')");
    expect(workflow).toContain("github.event.comment.author_association == 'MEMBER'");
    expect(workflow).toContain("github.event.comment.author_association == 'OWNER'");
    expect(workflow).toContain("github.event.comment.author_association == 'COLLABORATOR'");
  });

  it('copilot-review-gate dispatch reacts only to trusted bot marker comments', () => {
    const workflow = readWorkflow('copilot-review-gate.yml');
    expect(workflow).toContain("github.event_name == 'issue_comment'");
    expect(workflow).toContain('github.event.issue.pull_request');
    expect(workflow).toContain("contains(github.event.comment.body, '<!-- AE-COPILOT-AUTO-FIX v1 -->')");
    expect(workflow).toContain("github.event.comment.user.login == 'github-actions[bot]'");
  });

  it('pr-maintenance update-branch enforces fork guard and explicit mode', () => {
    const workflow = readWorkflow('pr-ci-status-comment.yml');
    expect(workflow).toContain("github.event.pull_request.head.repo.fork == false");
    expect(workflow).toContain("inputs.mode == 'update-branch'");
  });

  it('copilot-review-gate avoids PR comment writes on fork PRs', () => {
    const workflow = readWorkflow('copilot-review-gate.yml');
    expect(workflow).toContain('context.payload.pull_request?.head?.repo?.fork !== true');
    expect(workflow).toContain('Skipping PR comment (');
  });
});
