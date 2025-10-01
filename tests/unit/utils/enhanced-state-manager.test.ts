import { afterAll, describe, expect, it, vi } from 'vitest';
import { mkdtemp, rm, readFile, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { EnhancedStateManager } from '../../../src/utils/enhanced-state-manager.js';

const tempRoots: string[] = [];

afterAll(async () => {
  await Promise.all(tempRoots.map((dir) => rm(dir, { recursive: true, force: true })));
});


describe('EnhancedStateManager configuration', () => {
  it('applies default storage options when omitted', () => {
    const root = join(tmpdir(), 'ae-framework-config-default');
    const manager = new EnhancedStateManager(root);
    const options = (manager as any).options;

    expect(options.databasePath).toBe('.ae/enhanced-state.db');
    expect(options.enableCompression).toBe(true);
    expect(options.compressionThreshold).toBe(1024);
    expect(options.defaultTTL).toBe(86400 * 7);
    expect(options.gcInterval).toBe(3600);
    expect(options.maxVersions).toBe(10);
    expect(options.enableTransactions).toBe(true);

    const databaseFile = (manager as any).databaseFile as string;
    expect(databaseFile.endsWith('.ae/enhanced-state.db')).toBe(true);
  });

  it('respects provided storage options', () => {
    const root = join(tmpdir(), 'ae-framework-config-custom');
    const manager = new EnhancedStateManager(root, {
      databasePath: 'custom.db',
      enableCompression: false,
      compressionThreshold: 2048,
      defaultTTL: 3600,
      gcInterval: 120,
      maxVersions: 5,
      enableTransactions: false,
    });
    const options = (manager as any).options;

    expect(options.databasePath).toBe('custom.db');
    expect(options.enableCompression).toBe(false);
    expect(options.compressionThreshold).toBe(2048);
    expect(options.defaultTTL).toBe(3600);
    expect(options.gcInterval).toBe(120);
    expect(options.maxVersions).toBe(5);
    expect(options.enableTransactions).toBe(false);
  });
});

describe('EnhancedStateManager saveSSOT metadata', () => {
  it('honors provided tags, ttl, source, and phase', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-state-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, { databasePath: 'state.db', enableTransactions: false });

    const tags = { env: 'test', scope: 'reservation' };
    const key = await manager.saveSSOT('orders', { id: 'order-1' }, {
      tags,
      ttl: 120,
      source: 'cli',
      phase: 'verification',
    });

    const storage = (manager as unknown as { storage: Map<string, any> }).storage;
    const entry = storage.get(key);

    expect(entry?.tags).toEqual(tags);
    expect(entry?.ttl).toBe(120);
    expect(entry?.metadata?.source).toBe('cli');
    expect(entry?.metadata?.phase).toBe('verification');

    await manager.shutdown();
  });

  it('uses default metadata when options are omitted', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-state-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, { databasePath: 'state.db', enableTransactions: false });
    const key = await manager.saveSSOT('orders', { id: 'order-2' });

    const storage = (manager as unknown as { storage: Map<string, any> }).storage;
    const entry = storage.get(key);

    expect(entry?.tags).toEqual({});
    expect(entry?.ttl).toBe((manager as any).options.defaultTTL);
    expect(entry?.metadata?.source).toBe('unknown');

    await manager.shutdown();
  });
});


describe('EnhancedStateManager indices', () => {
  it('maintains key index and version history across multiple saves', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-state-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, { databasePath: 'state.db', enableTransactions: false });

    const firstKey = await manager.saveSSOT('inventory', { id: 'item', stock: 1 });
    await new Promise((resolve) => setTimeout(resolve, 5));
    const secondKey = await manager.saveSSOT('inventory', { id: 'item', stock: 2 });

    const keyIndex = (manager as unknown as { keyIndex: Map<string, Set<string>> }).keyIndex;
    const keys = keyIndex.get('inventory');
    expect(keys).not.toBeUndefined();
    expect(Array.from(keys ?? [])).toEqual(expect.arrayContaining([firstKey, secondKey]));

    const versions = await manager.getVersions('inventory');
    expect(versions.length).toBeGreaterThanOrEqual(2);
    expect(versions.map((v) => v.key)).toEqual(expect.arrayContaining([firstKey, secondKey]));
    expect(versions[0].version).toBeGreaterThan(versions[versions.length - 1].version);

    await manager.shutdown();
  });

  it('loads specific version when requested', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-state-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, { databasePath: 'state.db', enableTransactions: false });

    const first = await manager.saveSSOT('inventory', { id: 'item', stock: 10 });
    await new Promise(resolve => setTimeout(resolve, 5));
    await manager.saveSSOT('inventory', { id: 'item', stock: 15 });

    const versionOne = await manager.loadSSOT('inventory', 1);
    const versionTwo = await manager.loadSSOT('inventory', 2);

    expect(versionOne).toEqual({ id: 'item', stock: 10 });
    expect(versionTwo).toEqual({ id: 'item', stock: 15 });

    const keyIndex = (manager as unknown as { keyIndex: Map<string, Set<string>> }).keyIndex;
    expect(keyIndex.get('inventory')).toBeDefined();
    expect(Array.from(keyIndex.get('inventory') ?? [])).toContain(first);

    await manager.shutdown();
  });

  it('returns null when no entries exist for a logical key', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-state-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, { databasePath: 'state.db', enableTransactions: false });

    await expect(manager.loadSSOT('missing-key')).resolves.toBeNull();

    await manager.shutdown();
  });

  it('returns null when requesting an unknown version', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-state-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, { databasePath: 'state.db', enableTransactions: false });

    await manager.saveSSOT('inventory', { id: 'item', stock: 5 });

    const finder = manager as unknown as { findKeyByVersion: (logicalKey: string, version: number) => string | null };
    expect(finder.findKeyByVersion('inventory', 99)).toBeNull();

    await manager.shutdown();
  });

  it('returns null when requesting a version for an unseen logical key', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-state-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, { databasePath: 'state.db', enableTransactions: false });

    await expect(manager.loadSSOT('missing-key', 1)).resolves.toBeNull();

    await manager.shutdown();
  });

  it('ignores empty key sets when resolving latest versions', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-state-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, { databasePath: 'state.db', enableTransactions: false });

    const fullKey = await manager.saveSSOT('inventory', { id: 'item', stock: 1 });

    const internal = manager as unknown as {
      keyIndex: Map<string, Set<string>>;
      storage: Map<string, any>;
    };

    internal.storage.delete(fullKey);
    internal.keyIndex.set('inventory', new Set());

    await expect(manager.loadSSOT('inventory')).resolves.toBeNull();

    await manager.shutdown();
  });

  it('computes ttl expiry based on entry timestamp and seconds', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-state-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, { databasePath: 'state.db', enableTransactions: false, defaultTTL: 0 });

    const zeroTtlKey = await manager.saveSSOT('inventory', { id: 'item', stock: 3 });
    expect((manager as unknown as { ttlIndex: Map<string, number> }).ttlIndex.has(zeroTtlKey)).toBe(false);

    const ttlKey = await manager.saveSSOT('inventory', { id: 'item', stock: 4 }, { ttl: 90 });
    const ttlIndex = (manager as unknown as { ttlIndex: Map<string, number> }).ttlIndex;
    const expiry = ttlIndex.get(ttlKey);
    expect(typeof expiry).toBe('number');

    const storage = (manager as unknown as { storage: Map<string, any> }).storage;
    const entry = storage.get(ttlKey);
    const expectedExpiry = new Date(entry.timestamp).getTime() + (entry.ttl * 1000);
    expect(expiry).toBe(expectedExpiry);

    await manager.shutdown();
  });

  it('ignores stale index entries when resolving latest key', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-state-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, { databasePath: 'state.db', enableTransactions: false });

    const firstKey = await manager.saveSSOT('inventory', { id: 'item', stock: 1 });
    await new Promise(resolve => setTimeout(resolve, 10));
    const secondKey = await manager.saveSSOT('inventory', { id: 'item', stock: 5 });

    const internal = manager as unknown as { storage: Map<string, any> };
    internal.storage.delete(firstKey);

    const latestKey = (manager as any)['findLatestKey']('inventory');
    expect(latestKey).toBe(secondKey);

    await manager.shutdown();
  });

  it('prefers entries with strictly higher versions when versions tie', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-state-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, { databasePath: 'state.db', enableTransactions: false });

    const firstKey = await manager.saveSSOT('inventory', { id: 'item', stock: 10 });
    await new Promise(resolve => setTimeout(resolve, 10));
    const secondKey = await manager.saveSSOT('inventory', { id: 'item', stock: 20 });

    const internal = manager as unknown as { storage: Map<string, any> };
    const firstEntry = internal.storage.get(firstKey);
    const secondEntry = internal.storage.get(secondKey);
    if (firstEntry && secondEntry) {
      secondEntry.version = firstEntry.version;
    }

    const latestKey = (manager as any)['findLatestKey']('inventory');
    expect(latestKey).toBe(firstKey);

    await manager.shutdown();
  });

  it('lazily initializes on first access and skips redundant reinitialization', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-state-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, { databasePath: 'state.db', enableTransactions: false });
    const initializeSpy = vi.spyOn(manager as any, 'initialize');

    await expect(manager.loadSSOT('inventory')).resolves.toBeNull();
    expect(initializeSpy).toHaveBeenCalledTimes(1);

    initializeSpy.mockRestore();
    const redundantSpy = vi.spyOn(manager as any, 'initialize');

    await expect(manager.loadSSOT('inventory')).resolves.toBeNull();
    expect(redundantSpy).not.toHaveBeenCalled();

    redundantSpy.mockRestore();
    await manager.shutdown();
  });
});

describe('EnhancedStateManager transactions', () => {
  it('commits transactional save and persists entry', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-state-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, {
      databasePath: 'state.db',
      enableTransactions: true,
      gcInterval: 3600,
    });

    const txId = await manager.beginTransaction();
    const payload = { id: 'tx', value: 42 };

    await manager.saveSSOT('tx-entry', payload, { transactionId: txId });
    await manager.commitTransaction(txId);

    const restored = await manager.loadSSOT('tx-entry');
    expect(restored).toEqual(payload);
    expect(manager.getStatistics().activeTransactions).toBe(0);

    await manager.shutdown();
  });

  it('rolls back transactional changes when requested', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-state-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, {
      databasePath: 'state.db',
      enableTransactions: true,
      gcInterval: 3600,
    });

    const txId = await manager.beginTransaction();
    await manager.saveSSOT('rollback-entry', { id: 'rollback' }, { transactionId: txId });
    await manager.rollbackTransaction(txId);

    const restored = await manager.loadSSOT('rollback-entry');
    expect(restored).toBeNull();
    expect(manager.getStatistics().activeTransactions).toBe(0);

    await manager.shutdown();
  });

  it('cleans up expired entries during garbage collection', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-state-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, {
      databasePath: 'state.db',
      defaultTTL: 1,
      gcInterval: 1,
    });

    await manager.saveSSOT('ttl-entry', { id: 'ttl' }, { ttl: 1 });

    vi.useFakeTimers();
    vi.advanceTimersByTime(1500);
    await (manager as unknown as { runGarbageCollection: () => Promise<void> }).runGarbageCollection();
    vi.useRealTimers();

    const restored = await manager.loadSSOT('ttl-entry');
    expect(restored).toBeNull();

    await manager.shutdown();
  });

  it('keeps ttl entries alive before expiration is reached', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-state-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, {
      databasePath: 'state.db',
      defaultTTL: 0,
      gcInterval: 1,
    });

    await manager.saveSSOT('ttl-entry-active', { id: 'ttl' }, { ttl: 1 });

    await (manager as unknown as { runGarbageCollection: () => Promise<void> }).runGarbageCollection();

    const restored = await manager.loadSSOT('ttl-entry-active');
    expect(restored).toEqual({ id: 'ttl' });

    await manager.shutdown();
  });

  it('restores previous entry when rollback occurs on existing key', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-state-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, {
      databasePath: 'state.db',
      enableTransactions: true,
    });

    await manager.saveSSOT('inventory', { id: 'widget', stock: 2 });

    const txId = await manager.beginTransaction();
    await manager.saveSSOT('inventory', { id: 'widget', stock: 5 }, { transactionId: txId });

    await manager.rollbackTransaction(txId);

    const restored = await manager.loadSSOT('inventory');
    expect(restored).toEqual({ id: 'widget', stock: 2 });

    await manager.shutdown();
  });

  it('stores original entries once per key during rollback tracking', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-state-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, {
      databasePath: 'state.db',
      enableTransactions: true,
    });

    const fullKey = await manager.saveSSOT('inventory', { id: 'widget', stock: 2 });
    const internal = manager as unknown as {
      activeTransactions: Map<string, any>;
      saveInTransaction: (txId: string, key: string, entry: any) => Promise<void>;
      storage: Map<string, any>;
    };
    const originalEntry = internal.storage.get(fullKey);

    const txId = await manager.beginTransaction();
    const updatedEntry = { ...originalEntry, data: { id: 'widget', stock: 4 } };
    await internal.saveInTransaction(txId, fullKey, updatedEntry);
    const context = internal.activeTransactions.get(txId);
    expect(context.rollbackData.get(fullKey)).toEqual(originalEntry);

    const secondUpdate = { ...updatedEntry, data: { id: 'widget', stock: 6 } };
    await internal.saveInTransaction(txId, fullKey, secondUpdate);
    expect(context.rollbackData.get(fullKey)).toEqual(originalEntry);

    await manager.rollbackTransaction(txId);
    await manager.shutdown();
  });

  it('does not open new transaction when disabled globally', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-state-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, {
      databasePath: 'state.db',
      enableTransactions: false,
    });

    const beginSpy = vi.spyOn(manager, 'beginTransaction');

    await manager.saveSSOT('no-tx', { id: 'payload' });

    expect(beginSpy).not.toHaveBeenCalled();

    beginSpy.mockRestore();
    await manager.shutdown();
  });

  it('captures original entry for rollback when overwriting same key', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-state-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, {
      databasePath: 'state.db',
      enableTransactions: true,
    });

    const fullKey = await manager.saveSSOT('inventory', { id: 'widget', stock: 2 });
    const storage = (manager as unknown as { storage: Map<string, any> }).storage;
    const originalEntry = JSON.parse(JSON.stringify(storage.get(fullKey)));

    const txId = await manager.beginTransaction();
    const calculateChecksum = (manager as unknown as { calculateChecksum: (data: unknown) => string }).calculateChecksum.bind(manager);
    const updatedEntry = {
      ...storage.get(fullKey),
      data: { id: 'widget', stock: 9 },
      checksum: calculateChecksum({ id: 'widget', stock: 9 }),
    };

    await (manager as unknown as { saveInTransaction: (tx: string, key: string, entry: any) => Promise<void> }).saveInTransaction(txId, fullKey, updatedEntry);
    expect(storage.get(fullKey)?.data).toEqual({ id: 'widget', stock: 9 });

    await manager.rollbackTransaction(txId);

    expect(storage.get(fullKey)?.data).toEqual(originalEntry.data);
    await manager.shutdown();
  });

  it('throws when saving with an unknown transaction id', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-state-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, {
      databasePath: 'state.db',
      enableTransactions: true,
    });

    await expect(
      manager.saveSSOT('missing', { id: 'payload' }, { transactionId: 'nope' })
    ).rejects.toThrow('Transaction not found: nope');

    await manager.shutdown();
  });
});

describe('EnhancedStateManager compression behaviour', () => {
  it('compresses large payloads and restores original data', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-state-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, {
      compressionThreshold: 16,
      enableCompression: true,
      databasePath: 'state.db',
    });

    const payload = { id: 'demo', content: 'x'.repeat(256) };
    const key = await manager.saveSSOT('large-entry', payload);

    const storage = (manager as unknown as { storage: Map<string, unknown> }).storage;
    const entry: any = storage.get(key);
    expect(entry?.compressed).toBe(true);
    expect(entry?.data).toBeInstanceOf(Buffer);

    const restored = await manager.loadSSOT('large-entry');
    expect(restored).toEqual(payload);

    await manager.shutdown();
  });

  it('leaves small payloads uncompressed', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-state-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, {
      compressionThreshold: 1024,
      enableCompression: true,
      databasePath: 'state.db',
    });

    const tiny = { id: 'tiny', value: 1 };
    const key = await manager.saveSSOT('tiny-entry', tiny);

    const storage = (manager as unknown as { storage: Map<string, any> }).storage;
    const entry = storage.get(key);
    expect(entry?.compressed).toBe(false);
    expect(entry?.data).toEqual(tiny);

    await manager.shutdown();
  });

  it('does not compress payload when size equals threshold', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-state-'));
    tempRoots.push(root);

    const payload = { id: 'threshold', content: 'x'.repeat(32) };
    const serializedLength = JSON.stringify(payload).length;

    const manager = new EnhancedStateManager(root, {
      compressionThreshold: serializedLength,
      enableCompression: true,
      databasePath: 'state.db',
    });

    const key = await manager.saveSSOT('threshold-entry', payload);
    const storage = (manager as unknown as { storage: Map<string, any> }).storage;
    const entry = storage.get(key);

    expect(entry?.compressed).toBe(false);
    await manager.shutdown();
  });
});


describe('EnhancedStateManager snapshots and artifacts', () => {
  it('creates snapshots and restores entries', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-state-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, {
      databasePath: 'state.db',
      enableCompression: true,
      compressionThreshold: 32,
    });

    const createdSpy = vi.fn();
    manager.on('snapshotCreated', createdSpy);

    await manager.saveSSOT('inventory', { id: 'widget-1', stock: 5 });
    const snapshotId = await manager.createSnapshot('demo-phase', ['inventory']);

    expect(createdSpy).toHaveBeenCalledWith(
      expect.objectContaining({ snapshotId })
    );

    const snapshot = await manager.loadSnapshot(snapshotId);
    expect(snapshot).not.toBeNull();
    const keys = snapshot ? Object.keys(snapshot) : [];
    expect(keys.some(key => key.includes('inventory'))).toBe(true);

    await manager.shutdown();
  });

  it('persists failure artifacts and emits detailed events', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-state-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, { databasePath: 'state.db' });
    const persistedSpy = vi.fn();
    const typeSpy = vi.fn();
    const warnSpy = vi.spyOn(console, 'warn').mockImplementation(() => {});

    manager.on('failureArtifactPersisted', persistedSpy);
    manager.on('failure_validation', typeSpy);

    const artifact = {
      id: 'artifact-1',
      timestamp: new Date().toISOString(),
      phase: 'verification',
      type: 'validation',
      error: new Error('Schema mismatch'),
      context: { step: 'validate' },
      artifacts: ['report.json'],
      retryable: true,
      severity: 'medium' as const,
    };

    await manager.persistFailureArtifact(artifact);

    expect(persistedSpy).toHaveBeenCalledWith(
      expect.objectContaining({
        artifact,
        key: expect.stringMatching(/failure_verification_/),
        cegis_trigger: true,
      })
    );
    expect(typeSpy).toHaveBeenCalledWith(artifact);

    const storage = (manager as unknown as { storage: Map<string, any> }).storage;
    const persistedKey = persistedSpy.mock.calls[0][0].key;
    const entry = storage.get(persistedKey);
    expect(entry?.data).toEqual(artifact);
    expect(entry?.metadata?.source).toBe('failure_handler');

    warnSpy.mockRestore();
    await manager.shutdown();
  });
});


describe('EnhancedStateManager persistence and shutdown', () => {
  it('logs when no persistence data exists during initialization', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-state-'));
    tempRoots.push(root);

    const logSpy = vi.spyOn(console, 'log').mockImplementation(() => {});
    const manager = new EnhancedStateManager(root, { databasePath: 'state.db', enableTransactions: false });

    try {
      await manager.initialize();
      expect(logSpy).toHaveBeenCalledWith('📁 Starting with fresh state (no existing persistence file)');
    } finally {
      logSpy.mockRestore();
      manager.stopGarbageCollection();
    }
  });

  it('persists state to disk with exported entries', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-state-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, { databasePath: 'state.db' });
    await manager.initialize();

    await manager.saveSSOT('inventory', { id: 'widget-1', stock: 2 });
    await (manager as unknown as { persistToDisk: () => Promise<void> }).persistToDisk();

    const databaseFile = (manager as unknown as { databaseFile: string }).databaseFile;
    const persisted = JSON.parse(await readFile(databaseFile, 'utf8'));
    expect(Array.isArray(persisted.entries)).toBe(true);
    expect(persisted.entries.length).toBeGreaterThan(0);

    await manager.shutdown();
  });

  it('imports state from persistence when available', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-state-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, { databasePath: 'state.db' });
    await manager.initialize();
    await manager.saveSSOT('inventory', { id: 'widget-2', stock: 3 });
    await (manager as any).persistToDisk();
    await manager.shutdown();

    const second = new EnhancedStateManager(root, { databasePath: 'state.db' });

    try {
      await second.initialize();

      const restored = await second.loadSSOT('inventory');
      expect(restored).toEqual({ id: 'widget-2', stock: 3 });
    } finally {
      await second.shutdown();
    }
  });

  it('surfaces errors when persistence fails', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-state-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, { databasePath: 'state.db' });
    await manager.initialize();

    const error = new Error('disk full');
    const exportSpy = vi.spyOn(manager, 'exportState').mockRejectedValueOnce(error);
    const errorSpy = vi.spyOn(console, 'error').mockImplementation(() => {});

    await expect((manager as any).persistToDisk()).rejects.toThrow(error);
    expect(errorSpy).toHaveBeenCalledWith('Failed to persist state to disk:', error);

    exportSpy.mockRestore();
    errorSpy.mockRestore();
    await manager.shutdown();
  });

  it('flushes state and rolls back active transactions on shutdown', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-state-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, { databasePath: 'state.db' });
    await manager.initialize();

    const stopSpy = vi.spyOn(manager, 'stopGarbageCollection');
    const persistSpy = vi.spyOn(manager as unknown as { persistToDisk: () => Promise<void> }, 'persistToDisk').mockResolvedValue();
    const rollbackSpy = vi.spyOn(manager, 'rollbackTransaction');
    const shutdownSpy = vi.fn();
    manager.on('stateManagerShutdown', shutdownSpy);

    const txId = await manager.beginTransaction();
    await manager.saveSSOT('checkout', { id: 'order-1' }, { transactionId: txId });

    await manager.shutdown();

    expect(stopSpy).toHaveBeenCalledTimes(1);
    expect(persistSpy).toHaveBeenCalledTimes(1);
    expect(rollbackSpy).toHaveBeenCalledWith(txId);
    expect(shutdownSpy).toHaveBeenCalled();
    expect(manager.getStatistics().activeTransactions).toBe(0);

    stopSpy.mockRestore();
    persistSpy.mockRestore();
    rollbackSpy.mockRestore();
  });

  it('loads persistence without metadata block and logs restored entries', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-state-'));
    tempRoots.push(root);

    const timestamp = new Date().toISOString();
    const fullKey = `inventory_${timestamp}`;
    const persistence = {
      version: '1.0.0',
      entries: [
        {
          id: 'persisted-1',
          logicalKey: 'inventory',
          timestamp,
          version: 1,
          checksum: 'abc',
          data: { id: 'persisted-1', stock: 7 },
          compressed: false,
          tags: {},
          metadata: {
            size: 42,
            created: timestamp,
            accessed: timestamp,
            source: 'import-test',
          },
        },
      ],
      indices: {
        keyIndex: { inventory: [fullKey] },
        versionIndex: { inventory: 1 },
      },
    };

    await writeFile(join(root, 'state.db'), JSON.stringify(persistence));

    const logSpy = vi.spyOn(console, 'log').mockImplementation(() => {});
    const manager = new EnhancedStateManager(root, { databasePath: 'state.db', enableTransactions: false });

    await manager.initialize();

    expect(logSpy).toHaveBeenCalledWith('📁 Loaded 1 entries from persistence');
    await expect(manager.loadSSOT('inventory')).resolves.toEqual({ id: 'persisted-1', stock: 7 });

    logSpy.mockRestore();
    await manager.shutdown();
  });

  it('imports state when version metadata exists without top-level version', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-state-'));
    tempRoots.push(root);

    const timestamp = new Date().toISOString();
    const fullKey = `inventory_${timestamp}`;
    const persistence = {
      metadata: {
        version: '1.0.0',
        timestamp,
      },
      entries: [
        {
          id: 'metadata-only-1',
          logicalKey: 'inventory',
          timestamp,
          version: 3,
          checksum: 'meta-only',
          data: { id: 'metadata-only-1', stock: 11 },
          compressed: false,
          tags: {},
          metadata: {
            size: 64,
            created: timestamp,
            accessed: timestamp,
            source: 'metadata-import'
          }
        },
      ],
      indices: {
        keyIndex: { inventory: [fullKey] },
        versionIndex: { inventory: 3 },
      },
    };

    await writeFile(join(root, 'state.db'), JSON.stringify(persistence));

    const logSpy = vi.spyOn(console, 'log').mockImplementation(() => {});
    const manager = new EnhancedStateManager(root, { databasePath: 'state.db', enableTransactions: false });

    await manager.initialize();

    expect(logSpy).toHaveBeenCalledWith('📁 Loaded 1 entries from persistence');
    await expect(manager.loadSSOT('inventory')).resolves.toEqual({ id: 'metadata-only-1', stock: 11 });

    logSpy.mockRestore();
    await manager.shutdown();
  });

  it('imports state when metadata block is missing but version field exists', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-state-'));
    tempRoots.push(root);

    const timestamp = new Date().toISOString();
    const fullKey = `inventory_${timestamp}`;
    const persistence = {
      version: '1.0.0',
      entries: [
        {
          id: 'version-fallback-1',
          logicalKey: 'inventory',
          timestamp,
          version: 2,
          checksum: 'version-fallback-1',
          data: { id: 'version-fallback-1', stock: 6 },
          compressed: false,
          tags: {},
          metadata: {
            size: 48,
            created: timestamp,
            accessed: timestamp,
            source: 'version-test'
          }
        },
      ],
      indices: {
        keyIndex: { inventory: [fullKey] },
        versionIndex: { inventory: 2 },
      },
    };

    await writeFile(join(root, 'state.db'), JSON.stringify(persistence));

    const manager = new EnhancedStateManager(root, { databasePath: 'state.db', enableTransactions: false });

    await manager.initialize();

    await expect(manager.loadSSOT('inventory')).resolves.toEqual({ id: 'version-fallback-1', stock: 6 });

    await manager.shutdown();
  });

  it('reuses imported version index and emits entry count', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-state-'));
    tempRoots.push(root);

    const timestamp = new Date().toISOString();
    const fullKey = `inventory_${timestamp}`;
    const persistence = {
      version: '1.0.0',
      entries: [
        {
          id: 'persisted-versioned',
          logicalKey: 'inventory',
          timestamp,
          version: 7,
          checksum: 'persisted-versioned',
          data: { id: 'persisted-versioned', stock: 5 },
          compressed: false,
          tags: {},
          metadata: {
            size: 42,
            created: timestamp,
            accessed: timestamp,
            source: 'version-test'
          }
        }
      ],
      indices: {
        keyIndex: { inventory: [fullKey] },
        versionIndex: { inventory: 7 }
      }
    };

    await writeFile(join(root, 'state.db'), JSON.stringify(persistence));

    const manager = new EnhancedStateManager(root, { databasePath: 'state.db', enableTransactions: false });
    const importedSpy = vi.fn();
    manager.on('stateImported', importedSpy);

    await manager.initialize();

    expect(importedSpy).toHaveBeenCalledWith({ entryCount: 1 });

    const newKey = await manager.saveSSOT('inventory', { id: 'after-import', stock: 9 });
    const storage = (manager as unknown as { storage: Map<string, any> }).storage;
    const newEntry = storage.get(newKey);
    expect(newEntry?.version).toBe(8);

    await manager.shutdown();
  });

  it('restores ttl metadata when importing persistence entries', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-state-'));
    tempRoots.push(root);

    const timestamp = new Date().toISOString();
    const ttlSeconds = 120;
    const fullKey = `inventory_${timestamp}`;
    const persistence = {
      version: '1.0.0',
      entries: [
        {
          id: 'persisted-ttl',
          logicalKey: 'inventory',
          timestamp,
          version: 2,
          checksum: 'persisted-ttl',
          ttl: ttlSeconds,
          data: { id: 'persisted-ttl', stock: 3 },
          compressed: false,
          tags: {},
          metadata: {
            size: 64,
            created: timestamp,
            accessed: timestamp,
            source: 'ttl-test'
          }
        }
      ],
      indices: {
        keyIndex: { inventory: [fullKey] },
        versionIndex: { inventory: 2 }
      }
    };

    await writeFile(join(root, 'state.db'), JSON.stringify(persistence));

    const manager = new EnhancedStateManager(root, { databasePath: 'state.db', enableTransactions: false });
    await manager.initialize();

    const ttlIndex = (manager as unknown as { ttlIndex: Map<string, number> }).ttlIndex;
    const expiry = ttlIndex.get(fullKey);
    expect(expiry).toBeDefined();
    const expectedExpiry = new Date(timestamp).getTime() + ttlSeconds * 1000;
    expect(expiry).toBe(expectedExpiry);

    await manager.shutdown();
  });

  it('computes statistics with oldest/newest timestamps and averages', async () => {
    vi.useFakeTimers();
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-state-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, { databasePath: 'state.db', enableTransactions: false });
    await manager.initialize();

    try {
      vi.setSystemTime(new Date('2025-01-01T00:00:00Z'));
      await manager.saveSSOT('inventory', { id: 'first', stock: 1 });

      vi.setSystemTime(new Date('2025-01-01T01:00:00Z'));
      await manager.saveSSOT('inventory', { id: 'second', stock: 2 });

      const stats = manager.getStatistics();
      expect(stats.totalEntries).toBe(2);
      expect(stats.logicalKeys).toBe(1);
      expect(stats.averageVersions).toBeCloseTo(2);
      expect(stats.oldestEntry).toContain('2025-01-01T00:00:00');
      expect(stats.newestEntry).toContain('2025-01-01T01:00:00');
    } finally {
      vi.useRealTimers();
      await manager.shutdown();
    }
  });

  it('does not track ttl when entries omit ttl field', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-state-'));
    tempRoots.push(root);

    const timestamp = new Date().toISOString();
    const persistence = {
      version: '1.0.0',
      entries: [
        {
          id: 'persisted-no-ttl',
          logicalKey: 'inventory',
          timestamp,
          version: 1,
          checksum: 'no-ttl',
          data: { id: 'persisted-no-ttl', stock: 2 },
          compressed: false,
          tags: {},
          metadata: {
            size: 32,
            created: timestamp,
            accessed: timestamp,
            source: 'ttl-test'
          }
        }
      ],
      indices: {
        keyIndex: { inventory: [`inventory_${timestamp}`] },
        versionIndex: { inventory: 1 }
      }
    };

    await writeFile(join(root, 'state.db'), JSON.stringify(persistence));

    const manager = new EnhancedStateManager(root, { databasePath: 'state.db', enableTransactions: false });
    await manager.initialize();

    const ttlIndex = (manager as unknown as { ttlIndex: Map<string, number> }).ttlIndex;
    expect(ttlIndex.has(`inventory_${timestamp}`)).toBe(false);

    await manager.shutdown();
  });

  it('returns null oldest/newest statistics when no entries exist', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-state-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, { databasePath: 'state.db', enableTransactions: false });
    await manager.initialize();

    const stats = manager.getStatistics();
    expect(stats.totalEntries).toBe(0);
    expect(stats.oldestEntry).toBeNull();
    expect(stats.newestEntry).toBeNull();

    await manager.shutdown();
  });

  it('skips import when persistence version is unsupported', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-state-'));
    tempRoots.push(root);

    const timestamp = new Date().toISOString();
    const persistence = {
      version: '2.0.0',
      entries: [
        {
          id: 'future-1',
          logicalKey: 'inventory',
          timestamp,
          version: 1,
          checksum: 'future',
          data: { id: 'future-1', stock: 99 },
          compressed: false,
          tags: {},
          metadata: {
            size: 42,
            created: timestamp,
            accessed: timestamp,
            source: 'future',
          },
        },
      ],
      indices: {
        keyIndex: { inventory: [`inventory_${timestamp}`] },
        versionIndex: { inventory: 1 },
      },
    };

    await writeFile(join(root, 'state.db'), JSON.stringify(persistence));

    const importSpy = vi.fn();
    const logSpy = vi.spyOn(console, 'log').mockImplementation(() => {});
    const manager = new EnhancedStateManager(root, { databasePath: 'state.db', enableTransactions: false });
    manager.on('stateImported', importSpy);

    await manager.initialize();

    expect(importSpy).not.toHaveBeenCalled();
    expect(logSpy).not.toHaveBeenCalled();
    await expect(manager.loadSSOT('inventory')).resolves.toBeNull();

    logSpy.mockRestore();
    await manager.shutdown();
  });
});
