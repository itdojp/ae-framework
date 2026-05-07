import { Client, Connection } from '@temporalio/client';
import { approvalSignal, assuranceWorkflow } from './workflows.js';
import {
  DEFAULT_GENERATED_AT,
  DEFAULT_NAMESPACE,
  DEFAULT_REPOSITORY,
  DEFAULT_SCENARIO,
  DEFAULT_TASK_QUEUE,
} from './types.js';
import type { ApprovalPayload, WorkflowInput } from './types.js';

interface CliOptions {
  command: 'start' | 'signal-approval' | 'result' | 'help';
  workflowId: string;
  scenario: string;
  repository: string;
  prNumber: number | null;
  generatedAt: string;
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

function parseArgs(argv = process.argv.slice(2)): CliOptions {
  const command = (argv[0] ?? 'help') as CliOptions['command'];
  const options: CliOptions = {
    command: ['start', 'signal-approval', 'result'].includes(command) ? command : 'help',
    workflowId: `ae-assurance-${DEFAULT_SCENARIO}`,
    scenario: DEFAULT_SCENARIO,
    repository: DEFAULT_REPOSITORY,
    prNumber: 3247,
    generatedAt: DEFAULT_GENERATED_AT,
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
      options.prNumber = Number.parseInt(readValue(argv, index, arg), 10);
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

function usage(): void {
  console.log(`Usage:
  pnpm run start -- [options]
  pnpm run signal:approval -- [options]
  pnpm run result -- [options]

Common options:
  --workflow-id <id>             Workflow ID (default: ae-assurance-inventory-waiver)
  --scenario <name>              Fixture scenario (default: inventory-waiver)
  --address <host:port>          Temporal address (default: localhost:7233)
  --namespace <name>             Temporal namespace (default: default)
  --task-queue <name>            Temporal task queue (default: ae-assurance-temporal-poc)
  --generated-at <iso>           Deterministic generatedAt for fixture comparison
  --output-dir <path>            Output directory for generated artifacts
  --auto-approve                 Send the approval signal immediately after start
  --no-wait                      Start only; use signal/result commands later
`);
}

async function createClient(options: CliOptions): Promise<{ client: Client; connection: Connection }> {
  const connection = await Connection.connect({ address: options.address });
  const client = new Client({ connection, namespace: options.namespace });
  return { client, connection };
}

async function run(): Promise<void> {
  const options = parseArgs();
  if (options.command === 'help') {
    usage();
    return;
  }
  const { client, connection } = await createClient(options);
  try {
    if (options.command === 'start') {
      const workflowInput: WorkflowInput = {
        scenario: options.scenario,
        repository: options.repository,
        prNumber: options.prNumber,
        namespace: options.namespace,
        taskQueue: options.taskQueue,
        workflowId: options.workflowId,
        outputDir: options.outputDir,
        generatedAt: options.generatedAt,
        approval: { required: true, timeout: '24 hours' },
        restartValidationStatus: options.restartValidationStatus,
      };
      const handle = await client.workflow.start(assuranceWorkflow, {
        workflowId: options.workflowId,
        taskQueue: options.taskQueue,
        args: [workflowInput],
      });
      console.log(`Started workflowId=${handle.workflowId}`);
      if (options.autoApprove) {
        await handle.signal(approvalSignal, {
          ...options.approval,
          receivedAt: new Date().toISOString(),
        });
        console.log(`Sent approval signal to workflowId=${handle.workflowId}`);
      }
      if (options.wait) {
        const result = await handle.result();
        console.log(JSON.stringify(result, null, 2));
      }
      return;
    }

    const handle = client.workflow.getHandle(options.workflowId);
    if (options.command === 'signal-approval') {
      await handle.signal(approvalSignal, {
        ...options.approval,
        receivedAt: new Date().toISOString(),
      });
      console.log(`Sent approval signal to workflowId=${options.workflowId}`);
      return;
    }

    const result = await handle.result();
    console.log(JSON.stringify(result, null, 2));
  } finally {
    await connection.close();
  }
}

run().catch((error: unknown) => {
  console.error(error);
  process.exitCode = 1;
});
