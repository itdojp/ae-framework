import fs from 'node:fs';
import path from 'node:path';
import { describe, expect, it } from 'vitest';
import yaml from 'js-yaml';

const readWorkflow = (name: string) => fs.readFileSync(
  path.resolve(process.cwd(), '.github/workflows', name),
  'utf8',
);

type WorkflowDocument = {
  on?: {
    workflow_run?: {
      workflows?: string[];
    };
  };
};

const parseWorkflow = (name: string) => yaml.load(readWorkflow(name)) as WorkflowDocument;

const escapeRegExp = (value: string) => value.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');

const extractJobBlock = (workflow: string, jobName: string) => {
  const pattern = new RegExp(
    `(^|\\n)  ${escapeRegExp(jobName)}:\\n([\\s\\S]*?)(?=\\n  [A-Za-z0-9_-]+:\\n|$)`,
  );
  const match = workflow.match(pattern);
  if (!match) {
    throw new Error(`job block not found: ${jobName}`);
  }
  return `${match[1] || ''}  ${jobName}:\n${match[2]}`;
};

describe('workflow permission boundaries', () => {
  it('copilot-auto-fix blocks fork PRs and supports global kill-switch', () => {
    const workflow = readWorkflow('copilot-auto-fix.yml');
    expect(workflow).toContain('github.event.pull_request.head.repo.fork == false');
    expect(workflow).toContain('AE_AUTOMATION_GLOBAL_DISABLE');
  });

  it('codex-autopilot-lane issue_comment path requires trusted command + association + kill-switch', () => {
    const workflow = readWorkflow('codex-autopilot-lane.yml');
    expect(workflow).toContain("github.event.issue.pull_request");
    expect(workflow).toContain("contains(github.event.comment.body, '/autopilot run')");
    expect(workflow).toContain("github.event.comment.author_association == 'MEMBER'");
    expect(workflow).toContain("github.event.comment.author_association == 'OWNER'");
    expect(workflow).toContain("github.event.comment.author_association == 'COLLABORATOR'");
    expect(workflow).toContain('AE_AUTOMATION_GLOBAL_DISABLE');
  });

  it('agent-commands dispatches copilot-review-gate only for trusted bot marker comments', () => {
    const workflow = readWorkflow('agent-commands.yml');
    expect(workflow).toContain("const autoFixMarker = '<!-- AE-COPILOT-AUTO-FIX v1 -->'");
    expect(workflow).toContain("context.payload.comment?.user?.type === 'Bot'");
    expect(workflow).toContain("context.payload.comment?.user?.login === 'github-actions[bot]'");
    expect(workflow).toContain('body.includes(autoFixMarker)');
    expect(workflow).toContain("workflow_id: 'copilot-review-gate.yml'");
  });

  it('pr-maintenance update-branch enforces fork guard, explicit mode, and global kill-switch', () => {
    const workflow = readWorkflow('pr-ci-status-comment.yml');
    const updateBranch = extractJobBlock(workflow, 'update-branch');
    expect(updateBranch).toContain("github.event.pull_request.head.repo.fork == false");
    expect(updateBranch).toContain("inputs.mode == 'update-branch'");
    expect(updateBranch).toContain('AE_AUTOMATION_GLOBAL_DISABLE');
    expect(updateBranch).toContain('github-token: ${{ github.token }}');
  });

  it('keeps pull-request DoD report-only while preserving push/main enforcement', () => {
    const workflow = readWorkflow('quality-gates-centralized.yml');
    const dod = extractJobBlock(workflow, 'dod');
    expect(dod).toContain("continue-on-error: ${{ github.event_name == 'pull_request' }}");
    expect(dod).toContain('run: pnpm run quality:run -- --env=testing --gates=dod --sequential');
  });

  it('copilot-review-gate delegates fork-safe behavior to trusted script with explicit actor env', () => {
    const workflow = readWorkflow('copilot-review-gate.yml');
    expect(workflow).toContain('run: node scripts/ci/copilot-review-gate.mjs');
    expect(workflow).toContain('GH_TOKEN: ${{ secrets.GH_TOKEN || github.token }}');
    expect(workflow).toContain('PR_NUMBER: ${{ github.event.pull_request.number || github.event.issue.number || inputs.pr_number || \'\' }}');
    expect(workflow).toContain('AI_REVIEW_ACTORS');
  });

  it('policy-gate re-evaluates on Spec Generate & Model Tests workflow completion', () => {
    const workflow = parseWorkflow('policy-gate.yml');
    expect(workflow.on?.workflow_run).toBeDefined();
    expect(workflow.on?.workflow_run?.workflows).toContain('Spec Generate & Model Tests');
  });
});
