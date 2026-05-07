export const DEFAULT_TASK_QUEUE = 'ae-assurance-temporal-poc';
export const DEFAULT_NAMESPACE = 'default';
export const DEFAULT_SCENARIO = 'inventory-waiver';
export const DEFAULT_REPOSITORY = 'itdojp/ae-framework';

export type ArtifactKind =
  | 'execution-plan'
  | 'run-manifest'
  | 'verify-lite-run-summary'
  | 'assurance-summary'
  | 'claim-evidence-manifest'
  | 'policy-input'
  | 'policy-decision'
  | 'policy-gate-summary'
  | 'change-package-v2'
  | 'temporal-run-summary'
  | 'log'
  | 'other';

export type ArtifactStatus = 'present' | 'missing' | 'skipped' | 'generated';
export type ActivityStatus = 'completed' | 'failed' | 'skipped' | 'cancelled' | 'timed-out' | 'unknown';
export type WorkflowStatus = 'running' | 'completed' | 'failed' | 'cancelled' | 'terminated' | 'timed-out' | 'continued-as-new' | 'unknown';
export type SignalStatus = 'awaited' | 'received' | 'skipped' | 'timed-out';
export type RestartValidationStatus = 'not-run' | 'documented' | 'manual-pass' | 'automated-pass';

export interface ArtifactRef {
  id: string;
  kind: ArtifactKind;
  path: string;
  status: ArtifactStatus;
  schemaVersion?: string | null;
  description?: string;
}

export interface ApprovalPayload {
  approvedBy: string;
  waiverId?: string | null;
  expires?: string | null;
  reason?: string;
  receivedAt?: string;
}

export interface WorkflowInput {
  scenario?: string;
  repository?: string;
  prNumber?: number | null;
  namespace?: string;
  taskQueue?: string;
  workflowId?: string;
  outputDir?: string;
  generatedAt?: string;
  compareExpectedArtifacts?: boolean;
  approval?: {
    required?: boolean;
    timeout?: string;
  };
  restartValidationStatus?: RestartValidationStatus;
}

export interface OperationContext {
  scenario: string;
  repository: string;
  prNumber: number | null;
  inputRef: ArtifactRef;
  contractRefs: ArtifactRef[];
}

export interface ActivityResult {
  name: string;
  status: ActivityStatus;
  startedAt: string | null;
  completedAt: string | null;
  attempt: number;
  artifactRefs: ArtifactRef[];
  notes?: string[];
}

export interface SignalSummary {
  name: string;
  status: SignalStatus;
  awaitedAt: string | null;
  receivedAt: string | null;
  payloadSummary?: string;
  approvedBy?: string;
  waiverId?: string | null;
  expires?: string | null;
}

export interface TemporalRunSummary {
  schemaVersion: 'temporal-run-summary/v1';
  generatedAt: string;
  adapter: {
    name: string;
    version: string;
    placement: string;
    mandatoryDependency: boolean;
    sdk: {
      packages: Array<{
        name: '@temporalio/client' | '@temporalio/worker' | '@temporalio/workflow';
        version: string;
      }>;
    };
  };
  execution: {
    namespace: string;
    workflowType: string;
    workflowId: string;
    runId: string;
    taskQueue: string;
    status: WorkflowStatus;
    startedAt: string;
    completedAt: string | null;
  };
  operation: OperationContext;
  signals: {
    awaited: SignalSummary[];
    received: SignalSummary[];
  };
  activityResults: ActivityResult[];
  outputArtifacts: {
    verifyLiteRunSummary: ArtifactRef;
    assuranceSummary: ArtifactRef;
    claimEvidenceManifest: ArtifactRef;
    policyDecision: ArtifactRef;
    policyGateSummary?: ArtifactRef;
    changePackageV2?: ArtifactRef;
    temporalRunSummary: ArtifactRef;
  };
  history: {
    referenceType: 'temporal-cli-describe' | 'temporal-web-ui' | 'event-history-pointer' | 'other';
    namespace: string;
    workflowId: string;
    runId: string;
    pointer: string;
    notes?: string[];
  };
  restartValidation: {
    status: RestartValidationStatus;
    validatedAt?: string | null;
    evidenceRefs: ArtifactRef[];
    notes: string[];
  };
  summary: {
    activityCount: number;
    awaitedSignalCount: number;
    receivedSignalCount: number;
    outputArtifactCount: number;
    assuranceResult: 'pass' | 'waived' | 'report-only' | 'block' | 'unknown';
  };
}
