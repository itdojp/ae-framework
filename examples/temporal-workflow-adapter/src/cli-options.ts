import {
  DEFAULT_NAMESPACE,
  DEFAULT_REPOSITORY,
  DEFAULT_SCENARIO,
  DEFAULT_TASK_QUEUE,
} from './types.js';
import type { ApprovalPayload, WorkflowInput } from './types.js';

export interface CliOptions {
  command: 'start' | 'signal-approval' | 'result' | 'help';
  workflowId: string;
  scenario: string;
  repository: string;
  prNumber: number | null;
  generatedAt?: string;
  outputDir?: string;
  namespace: string;
  taskQueue: string;
  address: string;
  autoApprove: boolean;
  wait: boolean;
  restartValidationStatus?: WorkflowInput['restartValidationStatus'];
  approval: ApprovalPayload;
}

function readValue(argv: string[], index: number, option: string): string {
  const value = argv[index + 1];
  if (!value || value.startsWith('--')) {
    throw new Error(`${option} requires a value`);
  }
  return value;
}

function parseBool(value: string): boolean {
  return !['0', 'false', 'no'].includes(value.toLowerCase());
}

function parsePositiveInteger(value: string, option: string): number {
  if (!/^[1-9][0-9]*$/.test(value)) {
    throw new Error(`${option} requires a positive integer`);
  }
  const parsed = Number.parseInt(value, 10);
  if (!Number.isSafeInteger(parsed)) {
    throw new Error(`${option} is outside the supported integer range`);
  }
  return parsed;
}

export function parseArgs(argv = process.argv.slice(2)): CliOptions {
  const command = (argv[0] ?? 'help') as CliOptions['command'];
  const options: CliOptions = {
    command: ['start', 'signal-approval', 'result'].includes(command) ? command : 'help',
    workflowId: `ae-assurance-${DEFAULT_SCENARIO}`,
    scenario: DEFAULT_SCENARIO,
    repository: DEFAULT_REPOSITORY,
    prNumber: null,
    namespace: process.env.TEMPORAL_NAMESPACE ?? DEFAULT_NAMESPACE,
    taskQueue: process.env.TEMPORAL_TASK_QUEUE ?? DEFAULT_TASK_QUEUE,
    address: process.env.TEMPORAL_ADDRESS ?? 'localhost:7233',
    autoApprove: false,
    wait: command !== 'start',
    approval: {
      approvedBy: '@team-risk',
      waiverId: 'change-package-v2:waiver:0:manual-fraud-review',
      expires: '2099-12-31',
      reason: 'approval accepted for manual-fraud-review waiver',
    },
  };

  for (let index = 1; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--') {
      continue;
    }
    if (arg === '--workflow-id') {
      options.workflowId = readValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--scenario') {
      options.scenario = readValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--repository') {
      options.repository = readValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--pr-number') {
      options.prNumber = parsePositiveInteger(readValue(argv, index, arg), arg);
      index += 1;
      continue;
    }
    if (arg === '--generated-at') {
      options.generatedAt = readValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--output-dir') {
      options.outputDir = readValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--namespace') {
      options.namespace = readValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--task-queue') {
      options.taskQueue = readValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--address') {
      options.address = readValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--auto-approve') {
      options.autoApprove = true;
      options.wait = true;
      continue;
    }
    if (arg === '--wait') {
      options.wait = true;
      continue;
    }
    if (arg === '--no-wait') {
      options.wait = false;
      continue;
    }
    if (arg === '--restart-validation-status') {
      options.restartValidationStatus = readValue(argv, index, arg) as WorkflowInput['restartValidationStatus'];
      index += 1;
      continue;
    }
    if (arg === '--approved-by') {
      options.approval.approvedBy = readValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--waiver-id') {
      options.approval.waiverId = readValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--approval-reason') {
      options.approval.reason = readValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--approval-expires') {
      options.approval.expires = readValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg.startsWith('--auto-approve=')) {
      options.autoApprove = parseBool(arg.slice('--auto-approve='.length));
      if (options.autoApprove) options.wait = true;
      continue;
    }
    throw new Error(`Unknown argument: ${arg}`);
  }
  return options;
}

export function usage(): string {
  return `Usage:
  pnpm run start -- [options]
  pnpm run signal:approval -- [options]
  pnpm run result -- [options]

Common options:
  --workflow-id <id>             Workflow ID (default: ae-assurance-inventory-waiver)
  --scenario <name>              Fixture scenario (default: inventory-waiver)
  --address <host:port>          Temporal address (default: localhost:7233)
  --namespace <name>             Temporal namespace (default: default)
  --task-queue <name>            Temporal task queue (default: ae-assurance-temporal-poc)
  --generated-at <iso>           Override generatedAt; defaults to the Workflow start time
  --output-dir <path>            Output directory for generated artifacts
  --pr-number <number>           Optional PR number recorded in operation metadata
  --auto-approve                 Send the approval signal immediately after start
  --no-wait                      Start only; use signal/result commands later
`;
}
