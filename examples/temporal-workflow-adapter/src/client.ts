import { Client, Connection } from '@temporalio/client';
import { parseArgs, usage } from './cli-options.js';
import { approvalSignal, assuranceWorkflow } from './workflows.js';
import type { CliOptions } from './cli-options.js';
import type { WorkflowInput } from './types.js';

async function createClient(options: CliOptions): Promise<{ client: Client; connection: Connection }> {
  const connection = await Connection.connect({ address: options.address });
  const client = new Client({ connection, namespace: options.namespace });
  return { client, connection };
}

async function writeStream(stream: NodeJS.WriteStream, text: string): Promise<void> {
  await new Promise<void>((resolve, reject) => {
    stream.write(text, (error?: Error | null) => {
      if (error) reject(error);
      else resolve();
    });
  });
}

async function writeStdout(text: string): Promise<void> {
  await writeStream(process.stdout, text);
}

async function writeStderr(text: string): Promise<void> {
  await writeStream(process.stderr, text);
}

async function run(): Promise<void> {
  const options = parseArgs();
  if (options.command === 'help') {
    await writeStdout(usage());
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
        compareExpectedArtifacts: options.generatedAt !== undefined,
        approval: { required: true, timeout: '24 hours' },
        restartValidationStatus: options.restartValidationStatus,
      };
      const handle = await client.workflow.start(assuranceWorkflow, {
        workflowId: options.workflowId,
        taskQueue: options.taskQueue,
        args: [workflowInput],
      });
      await writeStdout(`Started workflowId=${handle.workflowId}\n`);
      if (options.autoApprove) {
        await handle.signal(approvalSignal, {
          ...options.approval,
          receivedAt: new Date().toISOString(),
        });
        await writeStdout(`Sent approval signal to workflowId=${handle.workflowId}\n`);
      }
      if (options.wait) {
        const result = await handle.result();
        await writeStdout(`${JSON.stringify(result, null, 2)}\n`);
      }
      return;
    }

    const handle = client.workflow.getHandle(options.workflowId);
    if (options.command === 'signal-approval') {
      await handle.signal(approvalSignal, {
        ...options.approval,
        receivedAt: new Date().toISOString(),
      });
      await writeStdout(`Sent approval signal to workflowId=${options.workflowId}\n`);
      return;
    }

    const result = await handle.result();
    await writeStdout(`${JSON.stringify(result, null, 2)}\n`);
  } finally {
    await connection.close();
  }
}

function exitAfterCli(status: number): void {
  // This standalone example is executed through tsx; force the process to
  // exit after awaited client cleanup so native SDK handles do not leave
  // documented one-shot commands hanging in local restart drills.
  process.exitCode = status;
  setImmediate(() => process.exit(status));
}

run()
  .then(() => exitAfterCli(0))
  .catch(async (error: unknown) => {
    const message = error instanceof Error && error.stack ? error.stack : String(error);
    try {
      await writeStderr(`${message}\n`);
    } finally {
      exitAfterCli(1);
    }
  });
