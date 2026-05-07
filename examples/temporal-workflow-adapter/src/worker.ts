import { NativeConnection, Worker } from '@temporalio/worker';
import { fileURLToPath } from 'node:url';
import * as activities from './activities.js';
import { DEFAULT_NAMESPACE, DEFAULT_TASK_QUEUE } from './types.js';

async function run(): Promise<void> {
  const address = process.env.TEMPORAL_ADDRESS ?? 'localhost:7233';
  const namespace = process.env.TEMPORAL_NAMESPACE ?? DEFAULT_NAMESPACE;
  const taskQueue = process.env.TEMPORAL_TASK_QUEUE ?? DEFAULT_TASK_QUEUE;
  const workflowsPath = fileURLToPath(new URL('./workflows.ts', import.meta.url));
  const connection = await NativeConnection.connect({ address });
  try {
    const worker = await Worker.create({
      connection,
      namespace,
      taskQueue,
      workflowsPath,
      activities,
    });
    console.log(`Temporal worker polling taskQueue=${taskQueue} namespace=${namespace} address=${address}`);
    await worker.run();
  } finally {
    await connection.close();
  }
}

run().catch((error: unknown) => {
  console.error(error);
  process.exitCode = 1;
});
