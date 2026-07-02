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
    workflow_dispatch?: {
      inputs?: Record<string, any>;
    };
    workflow_run?: {
      workflows?: string[];
    };
  };
  permissions?: Record<string, string> | 'read-all' | 'write-all';
  jobs?: Record<string, any>;
};

const parseWorkflow = (name: string) => yaml.load(readWorkflow(name)) as WorkflowDocument;
const workflowPermission = (workflow: WorkflowDocument, key: string) => (
  workflow.permissions && typeof workflow.permissions === 'object'
    ? workflow.permissions[key]
    : undefined
);

const escapeRegExp = (value: string) => value.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');

const extractAgentCommandsPrScript = () => {
  const workflow = parseWorkflow('agent-commands.yml');
  const steps = workflow.jobs?.handle_pr?.steps;
  if (!Array.isArray(steps)) {
    throw new Error('agent-commands handle_pr steps not found');
  }
  const scriptStep = steps.find((step) => step?.uses === 'actions/github-script@v7');
  const script = scriptStep?.with?.script;
  if (typeof script !== 'string' || script.length === 0) {
    throw new Error('agent-commands handle_pr github-script body not found');
  }
  return script;
};

const extractAgentCommandsIssueScript = () => {
  const workflow = parseWorkflow('agent-commands.yml');
  const steps = workflow.jobs?.handle_issue?.steps;
  if (!Array.isArray(steps)) {
    throw new Error('agent-commands handle_issue steps not found');
  }
  const scriptStep = steps.find((step) => step?.uses === 'actions/github-script@v7');
  const script = scriptStep?.with?.script;
  if (typeof script !== 'string' || script.length === 0) {
    throw new Error('agent-commands handle_issue github-script body not found');
  }
  return script;
};

const extractMutatingCommandSet = (prSection: string) => {
  const match = prSection.match(/const mutatingCommands = new Set\(\[([\s\S]*?)\]\);/);
  if (!match) {
    throw new Error('mutatingCommands set not found');
  }
  return new Set([...match[1].matchAll(/'([^']+)'/g)].map((item) => item[1]));
};

const extractMutatingIssueCommandSet = (issueSection: string) => {
  const match = issueSection.match(/const mutatingIssueCommands = new Set\(\[([\s\S]*?)\]\);/);
  if (!match) {
    throw new Error('mutatingIssueCommands set not found');
  }
  return new Set([...match[1].matchAll(/'([^']+)'/g)].map((item) => item[1]));
};

const detectPrCommandsThatReachMutationSinks = (script: string) => {
  const switchStart = script.indexOf('switch (cmd) {');
  const switchEnd = script.indexOf('default:', switchStart);
  if (switchStart < 0 || switchEnd < 0 || switchEnd <= switchStart) {
    throw new Error('agent-commands PR switch not found');
  }
  const switchBody = script.slice(switchStart, switchEnd);
  const mutating = new Set<string>();
  let activeCases: string[] = [];

  for (const line of switchBody.split('\n')) {
    const caseMatch = line.match(/case '([^']+)':/);
    if (caseMatch) {
      activeCases.push(caseMatch[1]);
      continue;
    }
    if (/(await\s+addLabels|await\s+removeLabel|await\s+removeLabelsByPrefix|await\s+dispatchWorkflow|dispatchWithResult\(|github\.rest\.issues\.addLabels|github\.rest\.issues\.removeLabel|github\.rest\.actions\.createWorkflowDispatch)/.test(line)) {
      for (const command of activeCases) {
        mutating.add(command);
      }
    }
    if (/^\s*return\b/.test(line)) {
      activeCases = [];
    }
  }

  return mutating;
};

const detectIssueCommandsThatReachMutationSinks = (script: string) => {
  const switchStart = script.indexOf('switch (cmd) {');
  const switchEnd = script.indexOf('default:', switchStart);
  if (switchStart < 0 || switchEnd < 0 || switchEnd <= switchStart) {
    throw new Error('agent-commands issue switch not found');
  }
  const switchBody = script.slice(switchStart, switchEnd);
  const mutating = new Set<string>();
  let activeCases: string[] = [];

  for (const line of switchBody.split('\n')) {
    const caseMatch = line.match(/case '([^']+)':/);
    if (caseMatch) {
      activeCases.push(caseMatch[1]);
      continue;
    }
    if (/(await\s+add\(|await\s+remove\(|await\s+assign\(|github\.rest\.issues\.addLabels|github\.rest\.issues\.removeLabel|github\.rest\.issues\.addAssignees|github\.rest\.issues\.createComment)/.test(line)) {
      for (const command of activeCases) {
        mutating.add(command);
      }
    }
    if (/^\s*return\b/.test(line)) {
      activeCases = [];
    }
  }

  return mutating;
};

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

  it('copilot-auto-fix runs trusted automation code in its write-scoped job', () => {
    const workflow = readWorkflow('copilot-auto-fix.yml');
    const parsed = parseWorkflow('copilot-auto-fix.yml');
    const autoFixJob = parsed.jobs?.['auto-fix'];
    const autoFixBlock = extractJobBlock(workflow, 'auto-fix');
    const steps = Array.isArray(autoFixJob?.steps) ? autoFixJob.steps : [];

    expect(parsed.permissions).toEqual({ contents: 'read' });
    expect(autoFixJob?.permissions).toEqual({
      contents: 'write',
      issues: 'write',
      'pull-requests': 'write',
    });

    const trustedCheckout = steps.find((step: any) => step?.name === 'Checkout trusted automation code');
    expect(trustedCheckout?.uses).toBe('actions/checkout@v4');
    expect(trustedCheckout?.with).toMatchObject({
      ref: '${{ github.event.pull_request.base.sha }}',
      path: 'trusted',
      'persist-credentials': false,
    });

    const prCheckout = steps.find((step: any) => step?.name === 'Checkout PR head workspace');
    expect(prCheckout?.uses).toBe('actions/checkout@v4');
    expect(prCheckout?.with).toMatchObject({
      ref: '${{ github.event.pull_request.head.sha }}',
      path: 'pr',
      'persist-credentials': false,
    });

    expect(autoFixBlock).not.toContain('uses: ./.github/actions/setup-node-pnpm');
    expect(autoFixBlock).toContain('uses: actions/setup-node@v4');
    expect(autoFixBlock).toContain('node trusted/scripts/ci/lib/automation-config.mjs');
    expect(autoFixBlock).toContain('working-directory: pr');
    expect(autoFixBlock).toContain('node ../trusted/scripts/ci/copilot-auto-fix.mjs');
    expect(autoFixBlock).not.toContain('run: node scripts/ci/copilot-auto-fix.mjs');

    const autoFixSource = fs.readFileSync(
      path.resolve(process.cwd(), 'scripts/ci/copilot-auto-fix.mjs'),
      'utf8',
    );
    expect(autoFixSource).toContain('const buildAuthenticatedGitEnv = () =>');
    expect(autoFixSource).toContain('GIT_CONFIG_COUNT');
    expect(autoFixSource).toContain('http.https://github.com/${repo}.git.extraheader');
    expect(autoFixSource).toContain("execFileSync('git', ['push', remoteUrl, refspec]");
    expect(autoFixSource).not.toContain("['push', 'origin'");
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

  it('agent-commands requires trusted PR commenters before label mutations or workflow dispatches', () => {
    const prScript = extractAgentCommandsPrScript();
    const mutatingCommands = extractMutatingCommandSet(prScript);
    const commandsThatReachMutationSinks = detectPrCommandsThatReachMutationSinks(prScript);

    expect(prScript).toContain("const trustedAssociations = ['MEMBER', 'OWNER', 'COLLABORATOR']");
    expect(prScript).toContain('const isTrusted = trustedAssociations.includes(association)');
    expect(prScript).toContain('assertTrustedForMutation');
    expect(prScript).toContain("assertTrustedForMutation('addLabels')");
    expect(prScript).toContain("assertTrustedForMutation('removeLabel')");
    expect(prScript).toContain("assertTrustedForMutation('removeLabelsByPrefix')");
    expect(prScript).toContain("assertTrustedForMutation('createWorkflowDispatch')");
    expect(prScript.indexOf('if (mutatingCommands.has(cmd)')).toBeGreaterThanOrEqual(0);
    expect(prScript.indexOf('if (mutatingCommands.has(cmd)')).toBeLessThan(prScript.indexOf('switch (cmd)'));
    expect(prScript).toContain('Permission denied for ${cmd');

    for (const command of commandsThatReachMutationSinks) {
      expect(mutatingCommands.has(command), `${command} must require trusted association`).toBe(true);
    }
    expect([...mutatingCommands].sort()).toEqual([...commandsThatReachMutationSinks].sort());
    expect(mutatingCommands.has('/formal-help')).toBe(false);
    expect(mutatingCommands.has('/formal-quickstart')).toBe(false);
  });

  it('agent-commands requires trusted issue commenters before label, assignee, or plan-comment mutations', () => {
    const issueScript = extractAgentCommandsIssueScript();
    const mutatingIssueCommands = extractMutatingIssueCommandSet(issueScript);
    const commandsThatReachMutationSinks = detectIssueCommandsThatReachMutationSinks(issueScript);

    expect(issueScript).toContain("const trustedAssociations = ['MEMBER', 'OWNER', 'COLLABORATOR']");
    expect(issueScript).toContain('const isTrusted = trustedAssociations.includes(association)');
    expect(issueScript).toContain('assertTrustedForIssueMutation');
    expect(issueScript).toContain("assertTrustedForIssueMutation('addLabels')");
    expect(issueScript).toContain("assertTrustedForIssueMutation('removeLabel')");
    expect(issueScript).toContain("assertTrustedForIssueMutation('addAssignees')");
    expect(issueScript).toContain("assertTrustedForIssueMutation('createComment')");
    expect(issueScript.indexOf('if (mutatingIssueCommands.has(cmd)')).toBeGreaterThanOrEqual(0);
    expect(issueScript.indexOf('if (mutatingIssueCommands.has(cmd)')).toBeLessThan(issueScript.indexOf('switch (cmd)'));
    expect(issueScript).toContain('Mutating issue commands require ${trustedAssociationText}');

    for (const command of commandsThatReachMutationSinks) {
      expect(mutatingIssueCommands.has(command), `${command} must require trusted association`).toBe(true);
    }
    expect([...mutatingIssueCommands].sort()).toEqual([...commandsThatReachMutationSinks].sort());
  });

  it('branch-protection admin workflow validates allowlisted inputs before ADMIN_TOKEN use', () => {
    const workflow = parseWorkflow('branch-protection-apply.yml');
    const rawWorkflow = readWorkflow('branch-protection-apply.yml');
    const inputs = workflow.on?.workflow_dispatch?.inputs ?? {};
    const job = workflow.jobs?.apply;
    const steps = Array.isArray(job?.steps) ? job.steps : [];
    const runBlocks = steps
      .map((step: any) => step?.run)
      .filter((run: unknown): run is string => typeof run === 'string')
      .join('\n');

    expect(inputs.preset?.type).toBe('choice');
    expect(inputs.preset?.default).toBe('branch-protection.main.require-verify-lite-gate.json');
    expect(inputs.preset?.default).not.toBe('branch-protection.main.relax2.json');
    expect(inputs.preset?.options).toContain('branch-protection.main.require-verify-lite-gate.json');
    expect(inputs.preset?.options).toContain('branch-protection.main.relax2.json');
    expect(inputs.branch?.type).toBe('choice');
    expect(inputs.branch?.options).toEqual(['main']);
    expect(inputs.emergency_approval?.type).toBe('choice');
    expect(inputs.emergency_approval?.options).toEqual(['normal-change', 'approved-break-glass']);
    expect(job?.environment?.name).toBe('branch-protection-admin');

    expect(runBlocks).toContain('node scripts/admin/validate-branch-protection-inputs.mjs');
    expect(runBlocks).not.toContain('github.event.inputs');
    expect(runBlocks).not.toMatch(/\$\{\{\s*inputs\.(branch|preset|emergency_approval)\s*\}\}/);
    expect(runBlocks).not.toContain('branches/${{');
    expect(rawWorkflow).toContain('secrets.BRANCH_PROTECTION_ADMIN_TOKEN');
    expect(rawWorkflow).not.toContain('secrets.ADMIN_TOKEN');
    expect(runBlocks).toContain('gh api "$BRANCH_PROTECTION_API_PATH"');
    expect(runBlocks).toContain('--input "$BRANCH_PROTECTION_PRESET_PATH"');

    const validateIndex = steps.findIndex((step: any) => step?.id === 'validate');
    const adminTokenStepIndices = steps
      .map((step: any, index: number) => ({ step, index }))
      .filter(({ step }) => String(step?.env?.GH_TOKEN ?? '').includes('secrets.BRANCH_PROTECTION_ADMIN_TOKEN'))
      .map(({ index }) => index);
    expect(validateIndex).toBeGreaterThanOrEqual(0);
    expect(adminTokenStepIndices.length).toBeGreaterThan(0);
    for (const index of adminTokenStepIndices) {
      expect(index).toBeGreaterThan(validateIndex);
    }
    expect(rawWorkflow).toContain('environment:\n      name: branch-protection-admin');
  });

  it('pr-maintenance renders PR summary read-only and publishes through a trusted workflow-run publisher', () => {
    const workflow = readWorkflow('pr-ci-status-comment.yml');
    const parsed = parseWorkflow('pr-ci-status-comment.yml');
    const summarize = extractJobBlock(workflow, 'summarize');
    const validateChangePackage = extractJobBlock(workflow, 'validate-change-package');
    const publisher = parseWorkflow('pr-summary-publisher.yml');
    const publisherRaw = readWorkflow('pr-summary-publisher.yml');
    const publisherJob = extractJobBlock(publisherRaw, 'publish');
    const enableAutoMerge = extractJobBlock(workflow, 'enable-auto-merge');

    expect(workflowPermission(parsed, 'issues')).toBeUndefined();
    expect(workflowPermission(parsed, 'pull-requests')).toBeUndefined();
    expect(parsed.jobs?.summarize?.permissions).toEqual({
      actions: 'read',
      contents: 'read',
      issues: 'read',
      'pull-requests': 'read',
    });
    const summarizeCheckout = parsed.jobs?.summarize?.steps?.find(
      (step: any) => step?.uses === 'actions/checkout@v4',
    );
    expect(summarizeCheckout?.with).toMatchObject({ 'persist-credentials': false });
    expect(parsed.jobs?.label?.permissions).toEqual({
      issues: 'write',
    });
    expect(parsed.jobs?.['validate-change-package']?.needs).toBe('summarize');
    expect(parsed.jobs?.['validate-change-package']?.permissions).toEqual({
      actions: 'read',
      contents: 'read',
    });
    expect(parsed.jobs?.['publish-summary']).toBeUndefined();
    expect(publisher.on?.workflow_run?.workflows).toContain('PR Maintenance');
    expect(publisher.permissions).toEqual({
      actions: 'read',
      checks: 'write',
      contents: 'read',
      issues: 'write',
      'pull-requests': 'read',
    });
    expect(summarize).toContain('Upload PR summary publish artifact');
    expect(summarize).toContain('Write PR summary publish provenance');
    expect(summarize).toContain('pr-summary-publish.provenance.json');
    expect(summarize).toContain('artifacts/change-package/change-package.json');
    expect(validateChangePackage).toContain('ref: ${{ github.event.pull_request.base.sha }}');
    expect(validateChangePackage).toContain('Install trusted validation dependencies');
    expect(validateChangePackage).toContain('pnpm install --frozen-lockfile --config.use-lockfile=true --config.package-lock=true');
    expect(validateChangePackage).toContain('Download PR summary publish artifact');
    expect(validateChangePackage).toContain('Validate Change Package with trusted base code');
    expect(validateChangePackage).toContain('node scripts/change-package/validate.mjs');
    expect(validateChangePackage).toContain('change-package-validation.provenance.json');
    expect(validateChangePackage).toContain('write-artifact-provenance.mjs');
    expect(validateChangePackage).toContain('trusted-change-package-validation-pr-${{ github.event.pull_request.number }}');
    expect(validateChangePackage).toContain("source: 'base-ref-code'");
    expect(summarize).not.toContain('issues.createComment');
    expect(summarize).not.toContain('issues.updateComment');
    expect(publisherJob).toContain('ref: ${{ github.event.repository.default_branch }}');
    expect(publisherJob).toContain('Download PR summary publish artifact');
    expect(publisherJob).toContain('Download trusted Change Package validation artifact');
    expect(publisherJob).toContain('Validate PR summary artifact provenance');
    expect(publisherJob).toContain('Validate trusted Change Package validation provenance');
    expect(publisherJob).toContain('validate-artifact-provenance.mjs');
    expect(publisherJob).toContain('--workflow "PR Maintenance"');
    expect(publisherJob).toContain('--workflow-ref-prefix "${GITHUB_REPOSITORY}/.github/workflows/pr-ci-status-comment.yml@"');
    expect(publisherJob).toContain('--require-subject summary/PR_SUMMARY.md');
    expect(publisherJob).toContain('--require-subject change-package-validation.json');
    expect(publisherJob).toContain("const trustedArtifactRoot = 'artifacts/publish/trusted-change-package'");
    expect(publisherJob).toContain("readText('summary/PR_SUMMARY.md')");
    expect(publisherJob).toContain("readText('progress/PR_PROGRESS.md')");
    expect(publisherJob).toContain("readJson('change-package-validation.json', trustedArtifactRoot)");
    expect(publisherJob).toContain("trusted.source !== 'base-ref-code'");
    expect(publisherJob).toContain("String(trusted.headSha || '') !== headSha");
    expect(publisherJob).toContain("String(trusted.workflowRunId || '') !== sourceRunId");
    expect(publisherJob).toContain('const truncateUtf8 = (text, maxBytes) =>');
    expect(publisherJob).toContain('MAX_COMMENT_BYTES - Buffer.byteLength(notice');
    expect(publisherJob).toContain('availableBytes');
    expect(publisherJob).toContain('const listAllIssueComments = async () =>');
    expect(publisherJob).toContain('page += 1');
    expect(publisherJob).toContain('let issueCommentsCache = null;');
    expect(publisherJob).toContain('const getIssueComments = async () =>');
    expect(publisherJob).toContain('issueCommentsCache = await listAllIssueComments();');
    expect(publisherJob).toContain('const isTrustedAutomationComment = (comment, marker) =>');
    expect(publisherJob).toContain("login === 'github-actions' || login === 'github-actions[bot]'");
    expect(publisherJob).toContain('body.startsWith(marker)');
    expect(publisherJob).toContain('const markerDisplayLabel = (marker) =>');
    expect(publisherJob).toContain("return label || 'PR comment';");
    expect(publisherJob).toContain('limitComment(`${marker}\\n\\n${body}`, markerDisplayLabel(marker))');
    expect(publisherJob).toContain('const comments = await getIssueComments();');
    expect(publisherJob).toContain('const existing = [...comments].reverse().find((comment) => isTrustedAutomationComment(comment, marker))');
    expect(publisherJob).toContain('Progress summary JSON omitted because it would exceed the PR comment size cap.');
    expect(publisherJob).toContain('Progress summary JSON could not be parsed; publishing Markdown without embedded JSON');
    expect(publisherJob).toContain('could not be parsed; treating as missing structured JSON');
    expect(publisherJob).toContain("name: 'Change Package Validation'");
    expect(publisherJob).toContain('head_sha: headSha');
    expect(enableAutoMerge).not.toContain("github.event_name == 'pull_request'");
  });

  it('auto-merge jobs consume Change Package check-run evidence instead of PR summary markdown', () => {
    const enablerSource = fs.readFileSync(
      path.resolve(process.cwd(), 'scripts/ci/auto-merge-enabler.mjs'),
      'utf8',
    );
    const eligibilitySource = fs.readFileSync(
      path.resolve(process.cwd(), 'scripts/ci/auto-merge-eligible.mjs'),
      'utf8',
    );
    expect(enablerSource).toContain('resolveChangePackageValidationStatusFromChecks(view.statusCheckRollup || [])');
    expect(enablerSource).not.toContain('resolveChangePackageValidationStatus(comments)');
    expect(enablerSource).toContain('missing change-package validation check');
    expect(enablerSource).toContain('ambiguous change-package validation checks');
    expect(eligibilitySource).toContain('resolveChangePackageValidationStatusFromChecks(pr.statusCheckRollup || [])');
    expect(eligibilitySource).not.toContain('resolveChangePackageValidationStatus(listComments');
    expect(eligibilitySource).not.toContain('const listComments');
    expect(eligibilitySource).toContain('change-package validation check pending');
    expect(eligibilitySource).toContain('ambiguous change-package validation checks');
  });

  it('pr-maintenance update-branch enforces fork guard, explicit mode, and global kill-switch', () => {
    const workflow = readWorkflow('pr-ci-status-comment.yml');
    const updateBranch = extractJobBlock(workflow, 'update-branch');
    const parsed = parseWorkflow('pr-ci-status-comment.yml');
    const inputs = parsed.on?.workflow_dispatch?.inputs ?? {};
    expect(updateBranch).toContain("github.event.pull_request.head.repo.fork == false");
    expect(updateBranch).toContain("inputs.mode == 'update-branch'");
    expect(updateBranch).toContain('AE_AUTOMATION_GLOBAL_DISABLE');
    expect(updateBranch).toContain('github-token: ${{ github.token }}');
    expect(inputs.expected_head_sha).toBeDefined();
    expect(updateBranch).toContain('expectedHeadSha');
    expect(updateBranch).toContain("workflow_dispatch update-branch requires expected_head_sha");
    expect(updateBranch).toContain("pr.head?.repo?.fork || headRepo !== expectedRepo");
    expect(updateBranch).toContain('headSha !== expectedHeadSha');
    expect(updateBranch).toContain('expected_head_sha: expectedHeadSha || pr.head.sha');
  });

  it('write-capable workflow_run maintenance validates same-repo current-head PRs before mutation', () => {
    const selfHealWorkflow = readWorkflow('pr-self-heal.yml');
    const autoRerunWorkflow = readWorkflow('ci-auto-rerun-failed.yml');
    const selfHealJob = extractJobBlock(selfHealWorkflow, 'self-heal');
    const autoRerunJob = extractJobBlock(autoRerunWorkflow, 'rerun-failed');

    expect(selfHealJob).toContain('WORKFLOW_RUN_HEAD_SHA');
    expect(selfHealJob).toContain('github.event.workflow_run.head_sha');
    expect(selfHealJob).toContain('WORKFLOW_RUN_HEAD_REPOSITORY');
    expect(selfHealJob).toContain('github.event.workflow_run.head_repository.full_name');
    expect(workflowPermission(parseWorkflow('pr-self-heal.yml'), 'pull-requests')).toBe('read');
    expect(workflowPermission(parseWorkflow('ci-auto-rerun-failed.yml'), 'pull-requests')).toBe('read');

    expect(autoRerunJob.indexOf('github.rest.pulls.get')).toBeGreaterThanOrEqual(0);
    expect(autoRerunJob.indexOf('github.rest.pulls.get')).toBeLessThan(autoRerunJob.indexOf('github.rest.actions.reRunWorkflowFailedJobs'));
    expect(autoRerunJob).toContain("currentPr.head?.repo?.fork || headRepo !== expectedRepo");
    expect(autoRerunJob).toContain('headSha !== workflowHeadSha');
    expect(autoRerunJob).toContain('workflowHeadRepo && workflowHeadRepo !== expectedRepo');
  });

  it('flake retry queries workflow runs with GET when passing gh api fields', () => {
    const workflow = readWorkflow('flake-detect.yml');
    const flakeRetryJob = extractJobBlock(workflow, 'flake-retry');

    expect(flakeRetryJob).toMatch(
      /gh api (?:--method GET|-X GET) "repos\/\$\{REPO\}\/actions\/workflows\/\$\{wf_id\}\/runs" -f per_page=10 -f status=completed/,
    );
    expect(flakeRetryJob).not.toContain(
      'gh api "repos/${REPO}/actions/workflows/${wf_id}/runs" -f per_page=10 -f status=completed',
    );
  });

  it('keeps pull-request DoD report-only while preserving push/main enforcement', () => {
    const workflow = readWorkflow('quality-gates-centralized.yml');
    const dod = extractJobBlock(workflow, 'dod');
    const publisher = parseWorkflow('quality-gates-publisher.yml');
    const publisherRaw = readWorkflow('quality-gates-publisher.yml');
    const publisherJob = extractJobBlock(publisherRaw, 'publish');
    expect(dod).toContain("continue-on-error: ${{ github.event_name == 'pull_request' }}");
    expect(dod).toContain('run: pnpm run quality:run -- --env=testing --gates=dod --sequential');
    expect(dod).toContain('Write quality report provenance');
    expect(dod).toContain('write-artifact-provenance.mjs');
    expect(workflow).not.toContain('  pr-quality-comment:');
    expect(publisher.on?.workflow_run?.workflows).toContain('Quality Gates');
    expect(publisher.permissions).toEqual({
      actions: 'read',
      contents: 'read',
      issues: 'write',
      'pull-requests': 'read',
    });
    expect(publisherJob).toContain('ref: ${{ github.event.repository.default_branch }}');
    expect(publisherJob).toContain('Validate quality report provenance');
    expect(publisherJob).not.toContain("sourceConclusion !== 'success'");
    expect(publisherJob).toContain('gh api --paginate "repos/$GITHUB_REPOSITORY/issues/$PR_NUMBER/comments"');
    expect(publisherJob).toContain('--workflow "Quality Gates"');
    expect(publisherJob).toContain('--workflow-ref-prefix "${GITHUB_REPOSITORY}/.github/workflows/quality-gates-centralized.yml@"');
    expect(publisherJob).toContain('validate-artifact-provenance.mjs');
    expect(publisherJob).toContain('render-quality-pr-comment.mjs');
    expect(publisherJob).toContain('gh api -X PATCH');
    expect(publisherJob).toContain('gh api -X POST');
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

  it('policy-gate downloads verify-lite assurance artifacts before label-derived strict mode', () => {
    const workflow = readWorkflow('policy-gate.yml');
    expect(workflow).toContain('actions: read');
    expect(workflow).toContain('persist-credentials: false');
    expect(workflow).toContain('PR_HEAD_SHA=');
    expect(workflow).toContain('head_sha=${PR_HEAD_SHA}');
    expect(workflow).toContain('PR_HEAD_REPOSITORY=');
    expect(workflow).toContain('head_repository=${PR_HEAD_REPOSITORY}');
    expect(workflow).toContain('Resolve assurance policy inputs');
    expect(workflow).toContain('assurance_escalation');
    expect(workflow).toContain('enforceAssuranceDecision');
    expect(workflow).toContain("labels.has('enforce-assurance')");
    expect(workflow).toContain("core.exportVariable('AE_POLICY_ASSURANCE_MODE', 'strict')");
    expect(workflow).toContain("core.exportVariable('AE_VERIFY_LITE_RUN_ID', String(run.id));");
    expect(workflow).toContain('AE_VERIFY_LITE_TRUSTED_GENERATOR_SHA256');
    expect(workflow).toContain('Download verify-lite assurance artifacts');
    expect(workflow).toContain('name: verify-lite-report');
    expect(workflow).toContain('path: artifacts');
    expect(workflow).toContain('run-id: ${{ steps.assurance-policy.outputs.verify_lite_run_id }}');
    expect(workflow).toContain('Write policy-gate artifact provenance');
    expect(workflow).toContain('Validate policy-gate artifact provenance');
    expect(workflow).toContain('policy-gate.provenance.json');
    expect(workflow).toContain('--artifact-name policy-gate-artifacts');
    expect(workflow).toContain('--workflow-ref-prefix "${GITHUB_REPOSITORY}/.github/workflows/policy-gate.yml@"');
    expect(workflow).toContain('--head-repository "${PR_HEAD_REPOSITORY}"');
    expect(workflow).toContain('--base-repository "${PR_BASE_REPOSITORY}"');
    expect(workflow).toContain('--require-subject ci/policy-gate-summary.json');
    expect(workflow).toContain('--require-subject ci/policy-decision-js-v1.json');
  });

  it('verify-lite records claim evidence provenance before uploading assurance artifacts', () => {
    const workflow = readWorkflow('verify-lite.yml');
    expect(workflow).toContain('persist-credentials: false');
    expect(workflow).toContain('Write claim evidence provenance (report-only)');
    expect(workflow).toContain('VERIFY_LITE_PR_HEAD_SHA');
    expect(workflow).toContain('node scripts/ci/write-verify-lite-assurance-provenance.mjs');
    expect(workflow).toContain('artifacts/agents/producer-normalization-summary.json');
    expect(workflow).toContain('artifacts/context-pack/boundary-map-summary.json');
    expect(workflow).toContain('artifacts/assurance/claim-evidence-provenance.json');
  });

  it('release workflows attest official SBOM and quality release assets before upload', () => {
    const release = parseWorkflow('release.yml');
    const releaseRaw = readWorkflow('release.yml');
    const releaseJob = release.jobs?.release;
    const releaseSteps = Array.isArray(releaseJob?.steps) ? releaseJob.steps : [];
    const releaseQualityJob = release.jobs?.['release-quality-artifacts'];

    expect(releaseJob?.permissions).toMatchObject({
      contents: 'write',
      packages: 'write',
      'id-token': 'write',
      attestations: 'write',
      'artifact-metadata': 'write',
    });
    expect(releaseQualityJob?.permissions).toMatchObject({
      contents: 'write',
      'id-token': 'write',
      attestations: 'write',
      'artifact-metadata': 'write',
    });

    const generateSbomIndex = releaseSteps.findIndex((step: any) => step?.name === 'Generate SBOM');
    const attestSbomIndex = releaseSteps.findIndex((step: any) => step?.name === 'Attest SBOM release asset');
    const stageSbomIndex = releaseSteps.findIndex((step: any) => step?.name === 'Stage SBOM attestation bundle');
    const createReleaseIndex = releaseSteps.findIndex((step: any) => step?.name === 'Create Release');
    const attestSbomStep = releaseSteps[attestSbomIndex];
    const stageSbomStep = releaseSteps[stageSbomIndex];
    const createReleaseStep = releaseSteps[createReleaseIndex];

    expect(generateSbomIndex).toBeGreaterThanOrEqual(0);
    expect(attestSbomIndex).toBeGreaterThan(generateSbomIndex);
    expect(stageSbomIndex).toBeGreaterThan(attestSbomIndex);
    expect(createReleaseIndex).toBeGreaterThan(stageSbomIndex);
    expect(attestSbomStep?.uses).toBe('actions/attest@v4');
    expect(attestSbomStep?.with?.['subject-path']).toBe('sbom.json');
    expect(stageSbomStep?.run).toContain('steps.attest_sbom.outputs.bundle-path');
    expect(stageSbomStep?.run).toContain('security/sigstore/sbom.intoto.jsonl');
    expect(createReleaseStep?.with?.files).toContain('sbom.json');
    expect(createReleaseStep?.with?.files).toContain('security/sigstore/sbom.intoto.jsonl');
    expect(releaseRaw).not.toContain('Placeholder for Sigstore signing');
    expect(releaseRaw).not.toContain('security/sigstore/*');

    const workflowLint = parseWorkflow('workflow-lint.yml');
    const actionlintSteps = Array.isArray(workflowLint.jobs?.actionlint?.steps)
      ? workflowLint.jobs.actionlint.steps
      : [];
    expect(actionlintSteps.some((step: any) => step?.uses === 'rhysd/actionlint@v1.7.12')).toBe(true);

    const quality = parseWorkflow('release-quality-artifacts.yml');
    const qualityRaw = readWorkflow('release-quality-artifacts.yml');
    const qualityJob = quality.jobs?.upload;
    const qualitySteps = Array.isArray(qualityJob?.steps) ? qualityJob.steps : [];

    expect(quality.permissions).toMatchObject({
      contents: 'write',
      'id-token': 'write',
      attestations: 'write',
      'artifact-metadata': 'write',
    });

    const prepareBundleIndex = qualitySteps.findIndex((step: any) => step?.name === 'Prepare bundle (include combined.json if present)');
    const attestQualityIndex = qualitySteps.findIndex((step: any) => step?.name === 'Attest quality artifact bundle');
    const stageQualityIndex = qualitySteps.findIndex((step: any) => step?.name === 'Stage quality attestation bundle');
    const uploadReleaseIndex = qualitySteps.findIndex((step: any) => step?.name === 'Upload release assets');
    const uploadManualIndex = qualitySteps.findIndex((step: any) => step?.name === 'Upload artifacts (manual)');
    const attestQualityStep = qualitySteps[attestQualityIndex];
    const stageQualityStep = qualitySteps[stageQualityIndex];
    const uploadReleaseStep = qualitySteps[uploadReleaseIndex];
    const uploadManualStep = qualitySteps[uploadManualIndex];

    expect(prepareBundleIndex).toBeGreaterThanOrEqual(0);
    expect(attestQualityIndex).toBeGreaterThan(prepareBundleIndex);
    expect(stageQualityIndex).toBeGreaterThan(attestQualityIndex);
    expect(uploadReleaseIndex).toBeGreaterThan(stageQualityIndex);
    expect(uploadManualIndex).toBeGreaterThan(stageQualityIndex);
    expect(attestQualityStep?.uses).toBe('actions/attest@v4');
    expect(attestQualityStep?.with?.['subject-path']).toBe('quality-artifacts.tgz');
    expect(stageQualityStep?.run).toContain('steps.attest_quality.outputs.bundle-path');
    expect(stageQualityStep?.run).toContain('security/sigstore/quality-artifacts.intoto.jsonl');
    expect(uploadReleaseStep?.with?.files).toContain('quality-artifacts.tgz');
    expect(uploadReleaseStep?.with?.files).toContain('security/sigstore/quality-artifacts.intoto.jsonl');
    expect(uploadManualStep?.with?.path).toContain('quality-artifacts.tgz');
    expect(uploadManualStep?.with?.path).toContain('security/sigstore/quality-artifacts.intoto.jsonl');
    expect(qualityRaw).toContain('actions/attest@v4');
  });

  it('release and dependency security workflows fail closed on lockfile and audit failures', () => {
    const releaseRaw = readWorkflow('release.yml');
    const securityRaw = readWorkflow('security.yml');
    const sbomRaw = readWorkflow('sbom-generation.yml');
    const protectedWorkflowText = [
      ['release.yml', releaseRaw],
      ['security.yml', securityRaw],
      ['sbom-generation.yml', sbomRaw],
    ] as const;

    for (const [workflowName, workflowText] of protectedWorkflowText) {
      expect(workflowText, `${workflowName} must not allow mutable dependency installs`).not.toContain('--no-frozen-lockfile');
      expect(workflowText, `${workflowName} must not suppress pnpm audit exits with || true`)
        .not.toMatch(/pnpm\s+audit[^\n]*\|\|\s*true/);
    }

    const release = parseWorkflow('release.yml');
    const releaseSteps = release.jobs?.release?.steps ?? [];
    const releaseInstallStep = Array.isArray(releaseSteps)
      ? releaseSteps.find((step: any) => step?.name === 'Install dependencies (frozen lockfile)')
      : undefined;
    expect(releaseInstallStep?.run).toBe('pnpm install --frozen-lockfile');
    expect(releaseInstallStep?.env).toMatchObject({
      NPM_CONFIG_USERCONFIG: '${{ github.workspace }}/.npmrc',
      NPM_CONFIG_GLOBALCONFIG: '/dev/null',
    });

    const security = parseWorkflow('security.yml');
    const dependencyAudit = security.jobs?.['dependency-audit'];
    const dependencyAuditSteps = dependencyAudit?.steps ?? [];
    const dependencyAuditInstallStep = Array.isArray(dependencyAuditSteps)
      ? dependencyAuditSteps.find((step: any) => step?.name === 'Install dependencies')
      : undefined;
    expect(dependencyAudit?.['continue-on-error']).toBe("${{ github.event_name == 'pull_request' && !contains(github.event.pull_request.labels.*.name, 'enforce-security') }}");
    expect(dependencyAuditInstallStep?.run).toBe(
      'pnpm install --frozen-lockfile --config.use-lockfile=true --config.package-lock=true'
    );
    expect(dependencyAuditInstallStep?.env).toMatchObject({
      NPM_CONFIG_USERCONFIG: '${{ github.workspace }}/.npmrc',
      NPM_CONFIG_GLOBALCONFIG: '/dev/null',
    });
    expect(securityRaw).toContain('pnpm audit --audit-level=moderate --json > audit-results.json');
    expect(securityRaw).toContain('Dependency audit did not produce parseable vulnerability metadata.');
    expect(securityRaw).toContain('High-risk vulnerabilities found under enforce-security mode.');
    expect(securityRaw).toContain('AUDIT_EXIT=$?');

    const sbom = parseWorkflow('sbom-generation.yml');
    const sbomSteps = sbom.jobs?.['sbom-generation']?.steps ?? [];
    const sbomInstallStep = Array.isArray(sbomSteps)
      ? sbomSteps.find((step: any) => step?.name === 'Install dependencies')
      : undefined;
    expect(sbomInstallStep?.run).toBe(
      'pnpm install --frozen-lockfile --config.use-lockfile=true --config.package-lock=true'
    );
    expect(sbomInstallStep?.env).toMatchObject({
      NPM_CONFIG_USERCONFIG: '${{ github.workspace }}/.npmrc',
      NPM_CONFIG_GLOBALCONFIG: '/dev/null',
    });
    expect(sbomRaw).toContain('High-risk vulnerabilities found under enforced SBOM audit mode.');
    expect(sbomRaw).toContain('printf \'{"metadata":{"vulnerabilities":{}}}\\n\' > audit-results.json');
  });

  it('SBOM pull request execution stays read-only and isolates publication credentials', () => {
    const sbom = parseWorkflow('sbom-generation.yml');
    const generationJob = sbom.jobs?.['sbom-generation'];
    const generationSteps = Array.isArray(generationJob?.steps) ? generationJob.steps : [];
    const generationCheckout = generationSteps.find((step: any) => step?.uses === 'actions/checkout@v4');

    expect(generationJob?.permissions).toMatchObject({
      contents: 'read',
      actions: 'read',
    });
    expect(generationJob?.permissions).not.toMatchObject({
      'security-events': 'write',
    });
    expect(Object.values(generationJob?.permissions ?? {})).not.toContain('write');
    expect(generationCheckout?.with).toMatchObject({
      'persist-credentials': false,
    });
    expect(generationSteps.some((step: any) => String(step?.uses ?? '').startsWith('./'))).toBe(true);
    expect(generationSteps.some((step: any) => String(step?.run ?? '').includes('pnpm run build'))).toBe(true);

    const publicationJob = sbom.jobs?.['sbom-publication'];
    const publicationSteps = Array.isArray(publicationJob?.steps) ? publicationJob.steps : [];
    expect(publicationJob?.if).toContain("github.event_name != 'pull_request'");
    expect(publicationJob?.if).toContain("github.ref == 'refs/heads/main'");
    expect(publicationJob?.permissions).toMatchObject({
      contents: 'read',
      actions: 'read',
    });
    expect(Object.values(publicationJob?.permissions ?? {})).not.toContain('write');
    expect(publicationSteps.some((step: any) => step?.uses === 'actions/checkout@v4')).toBe(false);
    expect(publicationSteps.some((step: any) => String(step?.uses ?? '').startsWith('./'))).toBe(false);
    expect(publicationSteps.find((step: any) => step?.name === 'Upload to Dependency Track')).toBeDefined();

    const analysisJob = sbom.jobs?.['security-analysis'];
    const analysisSteps = Array.isArray(analysisJob?.steps) ? analysisJob.steps : [];
    const analysisCheckout = analysisSteps.find((step: any) => step?.uses === 'actions/checkout@v4');
    expect(analysisJob?.permissions).toMatchObject({
      contents: 'read',
      actions: 'read',
    });
    expect(Object.values(analysisJob?.permissions ?? {})).not.toContain('write');
    expect(analysisCheckout?.with).toMatchObject({
      'persist-credentials': false,
    });
    expect(analysisSteps.some((step: any) => String(step?.uses ?? '').startsWith('github/codeql-action/'))).toBe(false);
    expect(analysisSteps.some((step: any) => step?.uses === 'actions/github-script@v7')).toBe(false);

    const codeqlJob = sbom.jobs?.['codeql-analysis'];
    const codeqlSteps = Array.isArray(codeqlJob?.steps) ? codeqlJob.steps : [];
    const codeqlCheckout = codeqlSteps.find((step: any) => step?.uses === 'actions/checkout@v4');
    expect(codeqlJob?.if).toContain("github.event_name != 'pull_request'");
    expect(codeqlJob?.if).toContain("github.ref == 'refs/heads/main'");
    expect(codeqlJob?.permissions).toMatchObject({
      contents: 'read',
      'security-events': 'write',
    });
    expect(codeqlCheckout?.with).toMatchObject({
      'persist-credentials': false,
    });

    expect(sbom.jobs?.['security-summary-comment']).toBeUndefined();
    expect(generationSteps.some((step: any) => step?.name === 'Write SBOM provenance')).toBe(true);
    expect(generationSteps.some((step: any) => step?.name === 'Write security scan provenance')).toBe(true);

    const publisher = parseWorkflow('sbom-security-publisher.yml');
    const publisherRaw = readWorkflow('sbom-security-publisher.yml');
    const publisherJob = extractJobBlock(publisherRaw, 'publish');
    expect(publisher.on?.workflow_run?.workflows).toContain('SBOM Generation and Security Scanning');
    expect(publisher.permissions).toMatchObject({
      contents: 'read',
      actions: 'read',
      issues: 'write',
      'pull-requests': 'read',
    });
    expect(publisherJob).toContain('ref: ${{ github.event.repository.default_branch }}');
    expect(publisherJob).toContain('Validate SBOM and security scan provenance');
    expect(publisherJob).toContain('validate-artifact-provenance.mjs');
    expect(publisherJob).toContain('--workflow "SBOM Generation and Security Scanning"');
    expect(publisherJob).toContain('--workflow-ref-prefix "${GITHUB_REPOSITORY}/.github/workflows/sbom-generation.yml@"');
    expect(publisherJob).toContain('--require-subject sbom.json');
    expect(publisherJob).toContain('--require-subject audit-results.json');
    expect(publisherJob).toContain('Post Security/Compliance summary');
    expect(publisherJob).toContain('github.paginate(github.rest.issues.listComments');
  });

  it('security analyzer pull request runs stay read-only and isolate security-events writes', () => {
    const security = parseWorkflow('security.yml');

    expect(security.permissions).toMatchObject({
      contents: 'read',
      actions: 'read',
    });
    expect(security.permissions).not.toMatchObject({
      'security-events': 'write',
    });

    const securityScanSteps = jobSteps(security, 'security-scan');

    expectReadOnlyJobPermissions(security, 'security-scan');
    expectCheckoutCredentialsDisabled(securityScanSteps);
    expect(securityScanSteps.some((step: any) => String(step?.uses ?? '').startsWith('./'))).toBe(false);
    expect(securityScanSteps.some((step: any) => String(step?.run ?? '').includes('pnpm run security:analyze')))
      .toBe(true);

    const codeqlJob = security.jobs?.['codeql-analysis'];
    const codeqlSteps = jobSteps(security, 'codeql-analysis');
    const codeqlCheckout = codeqlSteps.find((step: any) => step?.uses === 'actions/checkout@v4');
    expect(codeqlJob?.if).toContain("github.event_name != 'pull_request'");
    expect(codeqlJob?.permissions).toMatchObject({
      contents: 'read',
      actions: 'read',
      'security-events': 'write',
    });
    expect(codeqlCheckout?.with).toMatchObject({
      'persist-credentials': false,
    });

    const containerJob = security.jobs?.['container-security'];
    const containerSteps = jobSteps(security, 'container-security');
    const containerCheckout = containerSteps.find((step: any) => step?.uses === 'actions/checkout@v4');
    expect(containerJob?.if).toContain("github.event_name != 'pull_request'");
    expect(containerJob?.permissions).toMatchObject({
      contents: 'read',
      actions: 'read',
      'security-events': 'write',
    });
    expect(containerCheckout?.with).toMatchObject({
      'persist-credentials': false,
    });
    expect(containerSteps.some((step: any) => step?.uses === 'github/codeql-action/upload-sarif@v3')).toBe(true);
  });

  it('formal aggregate publishes PR comments from a separate trusted workflow-run publisher', () => {
    const aggregate = parseWorkflow('formal-aggregate.yml');
    const aggregateRaw = readWorkflow('formal-aggregate.yml');
    const verifyRaw = readWorkflow('formal-verify.yml');
    const verifyAggregate = extractJobBlock(verifyRaw, 'formal-aggregate');
    const publisher = parseWorkflow('formal-aggregate-publisher.yml');
    const publisherRaw = readWorkflow('formal-aggregate-publisher.yml');
    const publisherJob = extractJobBlock(publisherRaw, 'publish');
    const aggregateSteps = jobSteps(aggregate, 'aggregate');

    expect(workflowPermission(aggregate, 'issues')).toBeUndefined();
    expect(aggregate.on?.workflow_dispatch?.inputs?.pr_number).toBeUndefined();
    expect(aggregateRaw).not.toContain('Pull request number to comment on');
    expectReadOnlyJobPermissions(aggregate, 'aggregate');
    expectCheckoutCredentialsDisabled(aggregateSteps);
    expect(aggregateRaw).not.toContain('github.rest.issues');
    expect(aggregateRaw).not.toContain('issues.createComment');
    expect(aggregateRaw).not.toContain('issues.updateComment');
    expect(verifyAggregate).toContain('uses: ./.github/workflows/formal-aggregate.yml');
    expect(verifyAggregate).not.toContain('issues: write');

    expect(publisher.on?.workflow_run?.workflows).toContain('Formal Verify');
    expect(publisher.permissions).toMatchObject({
      actions: 'read',
      contents: 'read',
      issues: 'write',
      'pull-requests': 'read',
    });
    expect(jobSteps(publisher, 'publish').some((step) => step?.uses === 'actions/checkout@v4')).toBe(true);
    expect(publisherJob).toContain('ref: ${{ github.event.repository.default_branch }}');
    expect(jobSteps(publisher, 'publish').some((step) => String(step?.uses ?? '').startsWith('./'))).toBe(false);
    expect(publisher.on?.workflow_dispatch?.inputs?.pr_head_sha?.required).toBe(true);
    expect(publisher.on?.workflow_dispatch?.inputs?.source_run_attempt?.required).toBe(false);
    expect(publisherJob).toContain("workflowRun.head_sha");
    expect(publisherJob).toContain("workflowRun.run_attempt");
    expect(publisherJob).toContain('/^[0-9a-f]{40}$/i.test(expectedHeadSha)');
    expect(publisherJob).toContain('Invalid or missing PR head SHA');
    expect(publisherJob).toContain('workflowHeadRepository !== `${owner}/${repo}`');
    expect(publisherJob).toContain('pr.head.sha !== expectedHeadSha');
    expect(publisherJob).not.toContain('expectedHeadSha || pr.head.sha');
    expect(publisherJob).toContain("labels.has('run-formal')");
    expect(publisherJob).toContain('actions/download-artifact@v4');
    expect(publisherJob).toContain('run-id: ${{ steps.context.outputs.source_run_id }}');
    expect(publisherJob).toContain('Validate formal aggregate provenance');
    expect(publisherJob).toContain('validate-artifact-provenance.mjs');
    expect(publisherJob).toContain('--workflow "Formal Verify"');
    expect(publisherJob).toContain('--require-subject formal-aggregate.md');
    expect(publisherJob).toContain('FORMAL_AGGREGATE_MARKER');
    expect(publisherJob).toContain('MAX_COMMENT_BYTES');
    expect(publisherJob).toContain('sanitizeAggregateMarkdown');
    expect(publisherJob).toContain(".replace(/&/g, '&amp;')");
    expect(publisherJob).toContain('truncateUtf8');
    expect(publisherJob).toContain('listAllIssueComments');
    expect(publisherJob).toContain('isTrustedAutomationComment');
    expect(publisherJob).toContain("login === 'github-actions' || login === 'github-actions[bot]'");
    expect(publisherJob).toContain('startsWith(FORMAL_AGGREGATE_MARKER)');
  });

  it('dependency-track SBOM upload validates allowlisted HTTPS destinations before API-key use', () => {
    const sbom = parseWorkflow('sbom-generation.yml');
    const sbomSteps = sbom.jobs?.['sbom-publication']?.steps ?? [];
    const dependencyTrackStep = Array.isArray(sbomSteps)
      ? sbomSteps.find((step: any) => step?.name === 'Upload to Dependency Track')
      : undefined;
    const run = dependencyTrackStep?.run ?? '';

    expect(dependencyTrackStep?.env).toMatchObject({
      DT_ALLOWED_HOSTS: '${{ vars.DEPENDENCY_TRACK_ALLOWED_HOSTS }}',
    });
    const runLines = String(run).split('\n');
    const validatorInvocationIndex = runLines.findIndex((line) => line.trim() === 'validate_dependency_track_url');
    const apiKeyHeaderIndex = runLines.findIndex((line) => line.includes('-H "X-API-Key: $DT_API_KEY"'));
    expect(validatorInvocationIndex).toBeGreaterThanOrEqual(0);
    expect(validatorInvocationIndex).toBeLessThan(apiKeyHeaderIndex);
    expect(run).toContain('Dependency Track URL must use HTTPS');
    expect(run).toContain('Dependency Track URL must not contain userinfo');
    expect(run).toContain('DEPENDENCY_TRACK_ALLOWED_HOSTS');
    expect(run).toContain('--proto \'=https\'');
    expect(run).toContain('${DT_BASE_URL%/}/api/v1/bom');
    expect(run).not.toContain('$DT_BASE_URL/api/v1/bom');
  });
});

const jobSteps = (workflow: WorkflowDocument, jobName: string) => {
  const steps = workflow.jobs?.[jobName]?.steps;
  if (!Array.isArray(steps)) {
    throw new Error(`steps not found for ${jobName}`);
  }
  return steps;
};

const expectCheckoutCredentialsDisabled = (steps: any[]) => {
  const checkouts = steps.filter((step) => step?.uses === 'actions/checkout@v4');
  expect(checkouts.length).toBeGreaterThan(0);
  for (const checkout of checkouts) {
    expect(checkout.with).toMatchObject({ 'persist-credentials': false });
  }
};

const expectReadOnlyJobPermissions = (workflow: WorkflowDocument, jobName: string) => {
  expect(workflow.jobs?.[jobName]?.permissions).toMatchObject({
    contents: 'read',
    actions: 'read',
  });
  expect(workflow.jobs?.[jobName]?.permissions).not.toHaveProperty('issues');
  expect(workflow.jobs?.[jobName]?.permissions).not.toHaveProperty('pull-requests');
  expect(workflow.jobs?.[jobName]?.permissions).not.toHaveProperty('checks');
};

describe('CI workflow read-only PR validation boundaries', () => {
  it('Verify Traceability uses argv-safe Alloy arguments and read-only validation jobs', () => {
    const ci = parseWorkflow('ci.yml');
    expect(ci.jobs?.['verify-entry']?.permissions).toEqual({
      contents: 'read',
      actions: 'read',
      issues: 'write',
      'pull-requests': 'write',
    });
    expect(ci.jobs).not.toHaveProperty('verify-summary-publisher');

    const workflow = parseWorkflow('verify.yml');
    const raw = readWorkflow('verify.yml');
    expect(workflow.permissions).toMatchObject({ contents: 'read', actions: 'read' });
    expect(raw).not.toContain('ALLOY_RUN_CMD');
    expect(raw).toContain('ALLOY_CMD_JSON');

    for (const jobName of ['traceability', 'model-check', 'contracts-check', 'contracts-exec', 'formal-conformance-optin']) {
      expectReadOnlyJobPermissions(workflow, jobName);
      expectCheckoutCredentialsDisabled(jobSteps(workflow, jobName));
    }

    expectReadOnlyJobPermissions(workflow, 'build-summary');
    expect(jobSteps(workflow, 'build-summary').some((step) => step?.uses === 'actions/checkout@v4')).toBe(false);
    expect(jobSteps(workflow, 'build-summary').some((step) => step?.uses === 'actions/github-script@v7')).toBe(false);

    const postSummary = workflow.jobs?.['post-summary'];
    expect(postSummary?.if).toContain("inputs.trigger == 'pull_request'");
    expect(postSummary?.needs).toEqual(['build-summary']);
    expect(postSummary?.permissions).toMatchObject({
      actions: 'read',
      issues: 'write',
      'pull-requests': 'write',
    });
    expect(jobSteps(workflow, 'post-summary').some((step) => step?.uses === 'actions/checkout@v4')).toBe(false);
  });

  it('Spec Validation keeps PR validation read-only and publishes comments from a separate job', () => {
    const ci = parseWorkflow('ci.yml');
    expect(ci.jobs?.['spec-validation']?.permissions).toMatchObject({
      contents: 'read',
      actions: 'read',
      issues: 'write',
      'pull-requests': 'write',
    });
    expect(ci.jobs?.['build-test']).not.toHaveProperty('needs');
    expect(ci.jobs?.['build-test']?.if).toContain("inputs.mode == 'full'");
    expect(ci.jobs?.['build-test']?.if).not.toContain('needs.spec-validation');

    const workflow = parseWorkflow('spec-validation.yml');
    expect(workflow.permissions).toMatchObject({ contents: 'read', actions: 'read' });
    expect(workflow.permissions).not.toHaveProperty('pull-requests');

    expect(workflow.jobs?.['fail-fast-spec']?.permissions).toMatchObject({ contents: 'read', actions: 'read' });
    expect(workflow.jobs?.['spec-check']?.permissions).toMatchObject({ contents: 'read', actions: 'read' });
    expectReadOnlyJobPermissions(workflow, 'spec-validation');
    expectCheckoutCredentialsDisabled(jobSteps(workflow, 'spec-validation'));
    expect(jobSteps(workflow, 'spec-validation').some((step) => step?.uses === 'actions/github-script@v7')).toBe(false);

    const postJob = workflow.jobs?.['post-spec-validation-comment'];
    expect(postJob?.permissions).toMatchObject({
      actions: 'read',
      issues: 'write',
      'pull-requests': 'write',
    });
    expect(jobSteps(workflow, 'post-spec-validation-comment').some((step) => step?.uses === 'actions/checkout@v4')).toBe(false);

    const failFast = parseWorkflow('fail-fast-spec-validation.yml');
    expect(failFast.permissions).toMatchObject({ contents: 'read', actions: 'read' });
    expectCheckoutCredentialsDisabled(jobSteps(failFast, 'fail-fast-validation'));

    const specCheck = parseWorkflow('spec-check.yml');
    expect(specCheck.permissions).toMatchObject({ contents: 'read', actions: 'read' });
    expectReadOnlyJobPermissions(specCheck, 'tla');
    expectCheckoutCredentialsDisabled(jobSteps(specCheck, 'tla'));
  });

  it('Parallel E2E lane remains a no-op success on default PR runs', () => {
    const workflow = parseWorkflow('parallel-test-execution.yml');
    const testE2e = workflow.jobs?.['test-e2e'];
    expect(testE2e?.if).toContain("inputs.mode != 'coordinator'");
    expect(testE2e?.if).not.toContain('run-e2e');

    const steps = jobSteps(workflow, 'test-e2e');
    expect(steps[0]?.id).toBe('e2e');
    expect(steps[0]?.env?.SHOULD_RUN_E2E).toContain('run-e2e');
    expect(steps.some((step) => step?.name === 'Skip E2E tests' && String(step?.if).includes("should_run != 'true'"))).toBe(true);
    expect(steps.some((step) => step?.name === 'Run E2E tests' && String(step?.if).includes("should_run == 'true'"))).toBe(true);

    expect(workflow.jobs?.['test-consolidation']?.needs).toEqual(['test-matrix', 'test-e2e']);
  });

  it('Spec Generate and Model PR validation jobs are read-only and publication jobs do not checkout PR content', () => {
    const workflow = parseWorkflow('spec-generate-model.yml');
    expect(workflow.permissions).toMatchObject({ contents: 'read', actions: 'read' });
    expect(workflow.permissions).not.toHaveProperty('checks');
    expect(workflow.permissions).not.toHaveProperty('issues');
    expect(workflow.permissions).not.toHaveProperty('pull-requests');

    for (const jobName of ['generate-artifacts', 'model-based-tests', 'trace-conformance']) {
      expectReadOnlyJobPermissions(workflow, jobName);
      expectCheckoutCredentialsDisabled(jobSteps(workflow, jobName));
      expect(jobSteps(workflow, jobName).some((step) => step?.uses === 'actions/github-script@v7')).toBe(false);
    }

    const preview = workflow.jobs?.['publish-generate-artifacts-preview'];
    expect(preview?.permissions).toMatchObject({
      actions: 'read',
      issues: 'write',
      'pull-requests': 'write',
    });
    expect(jobSteps(workflow, 'publish-generate-artifacts-preview').some((step) => step?.uses === 'actions/checkout@v4')).toBe(false);

    const trace = workflow.jobs?.['publish-trace-summary'];
    expect(trace?.permissions).toMatchObject({
      actions: 'read',
      checks: 'write',
      issues: 'write',
      'pull-requests': 'write',
    });
    expect(jobSteps(workflow, 'publish-trace-summary').some((step) => step?.uses === 'actions/checkout@v4')).toBe(false);
  });
});
