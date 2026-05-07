import { spawn } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import type {
  ActivityResult,
  ApprovalPayload,
  ArtifactKind,
  ArtifactRef,
  OperationContext,
  SignalSummary,
  TemporalRunSummary,
  WorkflowInput,
} from './types.js';
import { DEFAULT_GENERATED_AT, DEFAULT_REPOSITORY, DEFAULT_SCENARIO } from './types.js';

const exampleRoot = fileURLToPath(new URL('..', import.meta.url));
const repoRoot = path.resolve(exampleRoot, '..', '..');

function nowIso(): string {
  return new Date().toISOString();
}

function normalizeScenario(input: WorkflowInput): string {
  return input.scenario ?? DEFAULT_SCENARIO;
}

function outputDirFor(input: WorkflowInput): string {
  const scenario = normalizeScenario(input);
  return path.resolve(repoRoot, input.outputDir ?? path.join('artifacts', 'temporal', scenario));
}

function toRepoPath(filePath: string): string {
  const relative = path.relative(repoRoot, filePath);
  if (relative && !relative.startsWith('..') && !path.isAbsolute(relative)) {
    return relative.split(path.sep).join('/');
  }
  return filePath.split(path.sep).join('/');
}

function ref(id: string, kind: ArtifactKind, filePath: string, schemaVersion: string | null, description: string, status: ArtifactRef['status'] = 'present'): ArtifactRef {
  return {
    id,
    kind,
    path: toRepoPath(filePath),
    status,
    schemaVersion,
    description,
  };
}

function scenarioFile(scenario: string, area: 'inputs' | 'expected', fileName: string): string {
  return path.resolve(repoRoot, 'fixtures', 'assurance-e2e', scenario, area, fileName);
}

function readJson(filePath: string): unknown {
  return JSON.parse(fs.readFileSync(filePath, 'utf8'));
}

function ensureFile(filePath: string, label: string): void {
  if (!fs.existsSync(filePath)) {
    throw new Error(`${label} not found: ${filePath}`);
  }
}

async function runNodeScript(args: string[]): Promise<void> {
  await new Promise<void>((resolve, reject) => {
    const child = spawn(process.execPath, args, {
      cwd: repoRoot,
      stdio: 'inherit',
      env: process.env,
    });
    child.on('error', reject);
    child.on('exit', (code) => {
      if (code === 0) {
        resolve();
      } else {
        reject(new Error(`node ${args.join(' ')} exited with ${code ?? 'unknown'}`));
      }
    });
  });
}

async function timedActivity(name: string, task: () => Promise<Omit<ActivityResult, 'name' | 'status' | 'startedAt' | 'completedAt' | 'attempt'>>): Promise<ActivityResult> {
  const startedAt = nowIso();
  const result = await task();
  return {
    name,
    status: 'completed',
    startedAt,
    completedAt: nowIso(),
    attempt: 1,
    ...result,
  };
}

export async function readOperationInput(input: WorkflowInput): Promise<OperationContext & { activity: ActivityResult }> {
  const scenario = normalizeScenario(input);
  const repository = input.repository ?? DEFAULT_REPOSITORY;
  const prNumber = input.prNumber ?? null;
  const changePackage = scenarioFile(scenario, 'inputs', 'change-package-v2.json');
  const verifyLite = scenarioFile(scenario, 'expected', 'verify-lite-run-summary.json');
  const assuranceSummary = scenarioFile(scenario, 'expected', 'assurance-summary.json');
  const policyDecision = scenarioFile(scenario, 'expected', 'policy-decision-js-v1.json');

  const activity = await timedActivity('readOperationInput', async () => {
    ensureFile(changePackage, 'change-package/v2 input');
    readJson(changePackage);
    return {
      artifactRefs: [
        ref('fixture-change-package-v2', 'change-package-v2', changePackage, 'change-package/v2', 'Operation input loaded by the Temporal adapter activity.'),
      ],
    };
  });

  return {
    scenario,
    repository,
    prNumber,
    inputRef: ref('fixture-change-package-v2', 'change-package-v2', changePackage, 'change-package/v2', 'Fixture operation input for the Temporal Workflow adapter PoC.'),
    contractRefs: [
      ref('verify-lite-run-summary', 'verify-lite-run-summary', verifyLite, '1.0.0', 'Existing verify-lite summary contract remains the source of truth.'),
      ref('assurance-summary', 'assurance-summary', assuranceSummary, 'assurance-summary/v1', 'Existing assurance summary contract remains the source of truth.'),
      ref('policy-decision-js-v1', 'policy-decision', policyDecision, '1.0.0', 'Waiver-aware policy decision consumed after approval signal receipt.'),
    ],
    activity,
  };
}

export async function preparePrerequisites(input: WorkflowInput): Promise<ActivityResult> {
  const scenario = normalizeScenario(input);
  return timedActivity('preparePrerequisites', async () => {
    const assuranceSummary = scenarioFile(scenario, 'inputs', 'assurance-summary.json');
    const qualityScorecard = scenarioFile(scenario, 'inputs', 'quality-scorecard.json');
    ensureFile(assuranceSummary, 'assurance-summary input');
    ensureFile(qualityScorecard, 'quality-scorecard input');
    return {
      artifactRefs: [
        ref('assurance-summary-input', 'assurance-summary', assuranceSummary, 'assurance-summary/v1', 'Prerequisite assurance summary fixture was found.'),
        ref('quality-scorecard-input', 'other', qualityScorecard, 'quality-scorecard/v1', 'Prerequisite quality scorecard fixture was found.'),
      ],
    };
  });
}

export async function runVerifyLite(input: WorkflowInput): Promise<ActivityResult> {
  const scenario = normalizeScenario(input);
  return timedActivity('runVerifyLite', async () => {
    const verifyLite = scenarioFile(scenario, 'expected', 'verify-lite-run-summary.json');
    ensureFile(verifyLite, 'verify-lite run summary');
    return {
      artifactRefs: [
        ref('verify-lite-run-summary', 'verify-lite-run-summary', verifyLite, '1.0.0', 'Fixture verify-lite summary was selected as lightweight verification evidence.'),
      ],
    };
  });
}

export async function runPolicyGate(input: WorkflowInput): Promise<ActivityResult> {
  const scenario = normalizeScenario(input);
  const generatedAt = input.generatedAt ?? DEFAULT_GENERATED_AT;
  const outputDir = outputDirFor(input);
  return timedActivity('runPolicyGate', async () => {
    fs.mkdirSync(outputDir, { recursive: true });
    await runNodeScript([
      'scripts/assurance/run-e2e-scenario.mjs',
      '--scenario', scenario,
      '--output-dir', outputDir,
      '--generated-at', generatedAt,
    ]);
    const policyDecision = path.join(outputDir, 'policy-decision-js-v1.json');
    const policyGateSummary = path.join(outputDir, 'policy-gate-summary.json');
    const claimEvidenceManifest = path.join(outputDir, 'claim-evidence-manifest.json');
    const assuranceSummary = path.join(outputDir, 'assurance-summary.json');
    ensureFile(policyDecision, 'policy decision output');
    return {
      artifactRefs: [
        ref('policy-decision-js-v1', 'policy-decision', policyDecision, '1.0.0', 'Policy decision reached waiver-aware assurance result.'),
        ref('policy-gate-summary', 'policy-gate-summary', policyGateSummary, 'policy-gate-summary/v1', 'Policy gate machine-readable summary.'),
        ref('claim-evidence-manifest', 'claim-evidence-manifest', claimEvidenceManifest, 'claim-evidence-manifest/v1', 'Claim evidence manifest generated by the fixture scenario.'),
        ref('assurance-summary', 'assurance-summary', assuranceSummary, 'assurance-summary/v1', 'Assurance summary copied by the fixture scenario.'),
      ],
      notes: ['The existing assurance E2E runner remains the producer of core JSON contracts.'],
    };
  });
}

function findRef(activityResults: ActivityResult[], id: string): ArtifactRef | undefined {
  for (const activity of activityResults) {
    const found = activity.artifactRefs.find((artifact) => artifact.id === id);
    if (found) return found;
  }
  return undefined;
}

function requiredRef(activityResults: ActivityResult[], id: string): ArtifactRef {
  const artifact = findRef(activityResults, id);
  if (!artifact) {
    throw new Error(`artifact ref not found: ${id}`);
  }
  return artifact;
}

export async function writeTemporalRunSummary(input: {
  workflow: {
    namespace: string;
    workflowType: string;
    workflowId: string;
    runId: string;
    taskQueue: string;
    startedAt: string;
  };
  operation: OperationContext;
  workflowInput: WorkflowInput;
  awaitedSignals: SignalSummary[];
  receivedSignals: SignalSummary[];
  activityResults: ActivityResult[];
  approval?: ApprovalPayload | null;
}): Promise<TemporalRunSummary> {
  return timedActivity('writeTemporalRunSummary', async () => {
    const outputDir = outputDirFor(input.workflowInput);
    fs.mkdirSync(outputDir, { recursive: true });
    const outputPath = path.join(outputDir, 'temporal-run-summary.json');
    const temporalRef = ref('temporal-run-summary', 'temporal-run-summary', outputPath, 'temporal-run-summary/v1', 'Temporal adapter sidecar summary.', 'generated');
    const generatedAt = input.workflowInput.generatedAt ?? nowIso();
    const activityResults = [
      ...input.activityResults,
      {
        name: 'writeTemporalRunSummary',
        status: 'completed' as const,
        startedAt: generatedAt,
        completedAt: generatedAt,
        attempt: 1,
        artifactRefs: [temporalRef],
      },
    ];
    const outputArtifacts = {
      verifyLiteRunSummary: requiredRef(activityResults, 'verify-lite-run-summary'),
      assuranceSummary: requiredRef(activityResults, 'assurance-summary'),
      claimEvidenceManifest: requiredRef(activityResults, 'claim-evidence-manifest'),
      policyDecision: requiredRef(activityResults, 'policy-decision-js-v1'),
      policyGateSummary: requiredRef(activityResults, 'policy-gate-summary'),
      changePackageV2: input.operation.inputRef,
      temporalRunSummary: temporalRef,
    };
    const summary: TemporalRunSummary = {
      schemaVersion: 'temporal-run-summary/v1',
      generatedAt,
      adapter: {
        name: 'ae-framework-temporal-workflow-adapter-poc',
        version: '0.1.0',
        placement: 'examples/temporal-workflow-adapter',
        mandatoryDependency: false,
        sdk: {
          name: '@temporalio/typescript-sdk',
          version: '1.17.0',
        },
      },
      execution: {
        namespace: input.workflow.namespace,
        workflowType: input.workflow.workflowType,
        workflowId: input.workflow.workflowId,
        runId: input.workflow.runId,
        taskQueue: input.workflow.taskQueue,
        status: 'completed',
        startedAt: input.workflow.startedAt,
        completedAt: generatedAt,
      },
      operation: input.operation,
      signals: {
        awaited: input.awaitedSignals,
        received: input.receivedSignals,
      },
      activityResults,
      outputArtifacts,
      history: {
        referenceType: 'temporal-cli-describe',
        namespace: input.workflow.namespace,
        workflowId: input.workflow.workflowId,
        runId: input.workflow.runId,
        pointer: `temporal workflow describe --namespace ${input.workflow.namespace} --workflow-id ${input.workflow.workflowId} --run-id ${input.workflow.runId}`,
        notes: ['Use a CLI or Web UI pointer instead of embedding full event history in the contract artifact.'],
      },
      restartValidation: {
        status: input.workflowInput.restartValidationStatus ?? 'documented',
        validatedAt: input.workflowInput.restartValidationStatus === 'manual-pass' || input.workflowInput.restartValidationStatus === 'automated-pass' ? generatedAt : null,
        evidenceRefs: [],
        notes: [
          'The PoC records restart evidence in this adapter sidecar. Operator restart drill steps are documented in docs/integrations/TEMPORAL-WORKFLOW-INTEGRATION.md.',
        ],
      },
      summary: {
        activityCount: activityResults.length,
        awaitedSignalCount: input.awaitedSignals.length,
        receivedSignalCount: input.receivedSignals.length,
        outputArtifactCount: Object.keys(outputArtifacts).length,
        assuranceResult: 'waived',
      },
    };
    fs.writeFileSync(outputPath, `${JSON.stringify(summary, null, 2)}\n`, 'utf8');
    return {
      artifactRefs: [temporalRef],
      notes: [`wrote ${toRepoPath(outputPath)}`],
    };
  }).then(() => readJson(path.join(outputDirFor(input.workflowInput), 'temporal-run-summary.json')) as TemporalRunSummary);
}
