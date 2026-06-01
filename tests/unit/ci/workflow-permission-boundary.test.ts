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

const extractMutatingCommandSet = (prSection: string) => {
  const match = prSection.match(/const mutatingCommands = new Set\(\[([\s\S]*?)\]\);/);
  if (!match) {
    throw new Error('mutatingCommands set not found');
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

  it('policy-gate downloads verify-lite assurance artifacts before label-derived strict mode', () => {
    const workflow = readWorkflow('policy-gate.yml');
    expect(workflow).toContain('actions: read');
    expect(workflow).toContain('Resolve assurance policy inputs');
    expect(workflow).toContain("labels.has('enforce-assurance')");
    expect(workflow).toContain("core.exportVariable('AE_POLICY_ASSURANCE_MODE', 'strict')");
    expect(workflow).toContain('Download verify-lite assurance artifacts');
    expect(workflow).toContain('name: verify-lite-report');
    expect(workflow).toContain('run-id: ${{ steps.assurance-policy.outputs.verify_lite_run_id }}');
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
    expect(dependencyAuditInstallStep?.run).toBe('pnpm install --frozen-lockfile');
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
    expect(sbomInstallStep?.run).toBe('pnpm install --frozen-lockfile');
    expect(sbomInstallStep?.env).toMatchObject({
      NPM_CONFIG_USERCONFIG: '${{ github.workspace }}/.npmrc',
      NPM_CONFIG_GLOBALCONFIG: '/dev/null',
    });
    expect(sbomRaw).toContain('High-risk vulnerabilities found under enforced SBOM audit mode.');
    expect(sbomRaw).toContain('printf \'{"metadata":{"vulnerabilities":{}}}\\n\' > audit-results.json');
  });
});
