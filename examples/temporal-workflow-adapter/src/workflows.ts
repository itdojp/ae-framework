import {
  condition,
  defineQuery,
  defineSignal,
  proxyActivities,
  setHandler,
  workflowInfo,
} from '@temporalio/workflow';
import type * as activities from './activities.js';
import type { ActivityResult, ApprovalPayload, SignalSummary, TemporalRunSummary, WorkflowInput } from './types.js';

export const approvalSignal = defineSignal<[ApprovalPayload]>('approval');
export const stateQuery = defineQuery<{
  awaitingApproval: boolean;
  receivedApproval: boolean;
  completedActivities: string[];
}>('state');

const {
  readOperationInput,
  preparePrerequisites,
  runVerifyLite,
  runPolicyGate,
  writeTemporalRunSummary,
} = proxyActivities<typeof activities>({
  startToCloseTimeout: '5 minutes',
  retry: {
    maximumAttempts: 3,
  },
});

function receivedApprovalSummary(approval: ApprovalPayload, awaitedAt: string | null): SignalSummary {
  return {
    name: 'approval',
    status: 'received',
    awaitedAt,
    receivedAt: approval.receivedAt ?? null,
    payloadSummary: approval.reason ?? 'approval signal received',
    approvedBy: approval.approvedBy,
    waiverId: approval.waiverId ?? null,
    expires: approval.expires ?? null,
  };
}

export async function assuranceWorkflow(input: WorkflowInput = {}): Promise<TemporalRunSummary> {
  const completedActivities: string[] = [];
  const activityResults: ActivityResult[] = [];
  const info = workflowInfo();
  const approvalRequired = input.approval?.required !== false;
  const approvalAwaitedAt = approvalRequired ? (input.generatedAt ?? info.startTime.toISOString()) : null;
  let approval: ApprovalPayload | undefined;

  setHandler(approvalSignal, (payload) => {
    approval = payload;
  });
  setHandler(stateQuery, () => ({
    awaitingApproval: approvalRequired && approval === undefined,
    receivedApproval: approval !== undefined,
    completedActivities,
  }));

  const operationResult = await readOperationInput(input);
  completedActivities.push(operationResult.activity.name);
  activityResults.push(operationResult.activity);

  const prerequisites = await preparePrerequisites(input);
  completedActivities.push(prerequisites.name);
  activityResults.push(prerequisites);

  const verifyLite = await runVerifyLite(input);
  completedActivities.push(verifyLite.name);
  activityResults.push(verifyLite);

  const awaitedSignals: SignalSummary[] = [];
  const receivedSignals: SignalSummary[] = [];
  if (approvalRequired) {
    awaitedSignals.push({
      name: 'approval',
      status: 'awaited',
      awaitedAt: approvalAwaitedAt,
      receivedAt: null,
      payloadSummary: 'waiting for waiver or approval signal before policy-gate activity',
    });
    const received = await condition(() => approval !== undefined, input.approval?.timeout ?? '24 hours');
    if (!received || approval === undefined) {
      awaitedSignals[0] = {
        ...awaitedSignals[0],
        status: 'timed-out',
      };
      throw new Error('approval signal timed out before policy-gate activity');
    }
    const summary = receivedApprovalSummary(approval, approvalAwaitedAt);
    awaitedSignals[0] = summary;
    receivedSignals.push(summary);
  } else {
    awaitedSignals.push({
      name: 'approval',
      status: 'skipped',
      awaitedAt: null,
      receivedAt: null,
      payloadSummary: 'approval signal disabled by workflow input',
    });
  }

  const policyGate = await runPolicyGate(input);
  completedActivities.push(policyGate.name);
  activityResults.push(policyGate);

  return await writeTemporalRunSummary({
    workflow: {
      namespace: info.namespace,
      workflowType: info.workflowType,
      workflowId: info.workflowId,
      runId: info.runId,
      taskQueue: info.taskQueue,
      startedAt: info.startTime.toISOString(),
    },
    operation: {
      scenario: operationResult.scenario,
      repository: operationResult.repository,
      prNumber: operationResult.prNumber,
      inputRef: operationResult.inputRef,
      contractRefs: operationResult.contractRefs,
    },
    workflowInput: input,
    awaitedSignals,
    receivedSignals,
    activityResults,
    approval: approval ?? null,
  });
}
