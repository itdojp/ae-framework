import { promises as fs } from 'fs';
import { mkdtemp } from 'fs/promises';
import { tmpdir } from 'os';
import { join } from 'path';
import type { TestAPI } from 'vitest';

export type IntegrationCleanupTask = () => void | Promise<void>;

type GlobalWithCleanup = typeof globalThis & {
  __aeIntegrationCleanup__?: IntegrationCleanupTask[];
};

const CLEANUP_KEY = '__aeIntegrationCleanup__';
const globalWithCleanup = globalThis as GlobalWithCleanup;

const ensureCleanupStore = (): IntegrationCleanupTask[] => {
  if (!globalWithCleanup[CLEANUP_KEY]) {
    globalWithCleanup[CLEANUP_KEY] = [];
  }
  return globalWithCleanup[CLEANUP_KEY]!;
};

export const resetIntegrationCleanupTasks = (): void => {
  globalWithCleanup[CLEANUP_KEY] = [];
};

export const drainIntegrationCleanupTasks = (): IntegrationCleanupTask[] => {
  const tasks = ensureCleanupStore();
  globalWithCleanup[CLEANUP_KEY] = [];
  return tasks;
};

export const registerIntegrationCleanup = (
  task: IntegrationCleanupTask,
): void => {
  ensureCleanupStore().push(task);
};

export const createIntegrationTempDir = async (
  prefix = 'ae-int-',
): Promise<string> => {
  const dir = await mkdtemp(join(tmpdir(), prefix));
  registerIntegrationCleanup(() =>
    fs.rm(dir, { recursive: true, force: true }),
  );
  return dir;
};

export const getIntegrationRetryAttempts = (): number => {
  const raw = process.env.AE_INTEGRATION_RETRY;
  if (!raw) {
    return 1;
  }
  const parsed = Number.parseInt(raw, 10);
  return Number.isFinite(parsed) && parsed > 0 ? parsed : 1;
};

export const applyIntegrationRetry = (target: Pick<TestAPI, 'retry'>): void => {
  const attempts = getIntegrationRetryAttempts();
  if (attempts > 1) {
    target.retry(attempts);
  }
};
