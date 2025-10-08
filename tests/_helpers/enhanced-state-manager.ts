import { mkdtemp, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import type { StorageOptions, StateEntry, EnhancedStateManager } from '../../src/utils/enhanced-state-manager.js';
import { EnhancedStateManager as Manager } from '../../src/utils/enhanced-state-manager.js';
import { createHash } from 'node:crypto';

export type TransactionOperation = {
  type: 'save' | 'delete';
  key: string;
  data?: StateEntry;
  previousData?: StateEntry;
};

export type TransactionContext = {
  operations: TransactionOperation[];
  rollbackData: Map<string, StateEntry>;
};

export type EnhancedStateManagerInternal = EnhancedStateManager & {
  options: EnhancedStateManager['options'];
  databaseFile: string;
  storage: Map<string, StateEntry>;
  keyIndex: Map<string, Set<string>>;
  ttlIndex: Map<string, number>;
  versionIndex: Map<string, number>;
  activeTransactions: Map<string, TransactionContext>;
  saveInTransaction: (txId: string, key: string, entry: StateEntry) => Promise<void>;
  findKeyByVersion: (logicalKey: string, version: number) => string | null;
  findLatestKey: (logicalKey: string) => string | null;
  initialize: () => Promise<void>;
  runGarbageCollection: () => Promise<void>;
  persistToDisk: () => Promise<void>;
  calculateChecksum: (data: unknown, serializedHint?: string) => string;
  decompress: (buffer: Buffer) => Promise<unknown>;
  stringifyForStorage: (value: unknown, context?: string) => string;
  measureSerializedSize: (serializedData: string) => number;
};

export const asInternal = (manager: EnhancedStateManager): EnhancedStateManagerInternal => manager as unknown as EnhancedStateManagerInternal;

export const getStorage = (manager: EnhancedStateManager) => asInternal(manager).storage;
export const getTransactions = (manager: EnhancedStateManager) => asInternal(manager).activeTransactions;
export const getOptions = (manager: EnhancedStateManager) => asInternal(manager).options;
export const getKeyIndex = (manager: EnhancedStateManager) => asInternal(manager).keyIndex;
export const getVersionIndex = (manager: EnhancedStateManager) => asInternal(manager).versionIndex;

export type ExportedState = Awaited<ReturnType<EnhancedStateManager['exportState']>>;

export const buildExportedState = (
  manager: EnhancedStateManager,
  overrides: {
    metadata?: Partial<ExportedState['metadata']>;
    entries?: StateEntry[];
    indices?: Partial<ExportedState['indices']>;
  } = {}
): ExportedState => {
  const base: ExportedState = {
    metadata: {
      version: '1.0.0',
      timestamp: new Date().toISOString(),
      options: getOptions(manager),
    },
    entries: [],
    indices: {
      keyIndex: {},
      versionIndex: {},
    },
  };

  return {
    ...base,
    ...overrides,
    metadata: {
      ...base.metadata,
      ...overrides.metadata,
    },
    entries: overrides.entries ?? base.entries,
    indices: {
      keyIndex: overrides.indices?.keyIndex ?? base.indices.keyIndex,
      versionIndex: overrides.indices?.versionIndex ?? base.indices.versionIndex,
    },
  };
};

export const buildStateEntry = <T = unknown>(
  logicalKey: string,
  data: T,
  overrides: {
    id?: string;
    timestamp?: string;
    version?: number;
    checksum?: string;
    compressed?: boolean;
    tags?: Record<string, string>;
    ttl?: number;
    metadata?: Partial<StateEntry['metadata']>;
  } = {}
): StateEntry<T> => {
  const timestamp = overrides.timestamp ?? new Date().toISOString();
  const size = (() => {
    if (Buffer.isBuffer(data)) {
      return data.length;
    }
    try {
      return JSON.stringify(data).length;
    } catch {
      return Array.isArray(data) ? data.length : 0;
    }
  })();
  const checksum = (() => {
    if (overrides.checksum !== undefined) {
      return overrides.checksum;
    }
    if (Buffer.isBuffer(data)) {
      return createHash('sha256').update(data).digest('hex');
    }
    try {
      return createHash('sha256').update(JSON.stringify(data)).digest('hex');
    } catch {
      return '';
    }
  })();

  return {
    id: overrides.id ?? createHash('md5').update(`${logicalKey}:${timestamp}:${size}`).digest('hex'),
    logicalKey,
    timestamp,
    version: overrides.version ?? 1,
    checksum,
    data,
    compressed: overrides.compressed ?? false,
    tags: overrides.tags ?? {},
    ttl: overrides.ttl,
    metadata: {
      size,
      created: overrides.metadata?.created ?? timestamp,
      accessed: overrides.metadata?.accessed ?? timestamp,
      source: overrides.metadata?.source ?? 'test',
      phase: overrides.metadata?.phase,
    },
  };
};

export const createTempProjectRoot = async (prefix = 'ae-enhanced-state-') => mkdtemp(join(tmpdir(), prefix));

export const cleanupProjectRoot = async (root?: string) => {
  if (!root) return;
  await rm(root, { recursive: true, force: true });
};

export const createManager = (projectRoot: string, options: StorageOptions = {}) => new Manager(projectRoot, options);
