import { afterAll, describe, expect, it, vi } from 'vitest';
import { mkdtemp, mkdir, rm, readFile, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { gzipSync } from 'node:zlib';
import { createHash } from 'node:crypto';
import { EnhancedStateManager } from '../../../src/utils/enhanced-state-manager.js';
import type { StateEntry } from '../../../src/utils/enhanced-state-manager.js';
import { asInternal, getStorage, getTransactions, getOptions, getKeyIndex, getVersionIndex, buildExportedState, buildStateEntry } from '../../_helpers/enhanced-state-manager.js';

const tempRoots: string[] = [];

afterAll(async () => {
  await Promise.all(tempRoots.map((dir) => rm(dir, { recursive: true, force: true })));
});
describe('EnhancedStateManager configuration', () => {
  it('applies default storage options when omitted', () => {
    const root = join(tmpdir(), 'ae-framework-config-default');
    const manager = new EnhancedStateManager(root);
    const options = getOptions(manager);

    expect(options.databasePath).toBe('.ae/enhanced-state.db');
    expect(options.enableCompression).toBe(true);
    expect(options.compressionThreshold).toBe(1024);
    expect(options.defaultTTL).toBe(86400 * 7);
    expect(options.gcInterval).toBe(3600);
    expect(options.maxVersions).toBe(10);
    expect(options.enableTransactions).toBe(true);
    expect(options.enablePerformanceMetrics).toBe(false);
    expect(options.enableSerializationCache).toBe(false);
    expect(options.performanceSampleSize).toBe(20);
    expect(options.skipUnchangedPersistence).toBe(true);

    const databaseFile = asInternal(manager).databaseFile as string;
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
      enablePerformanceMetrics: true,
      enableSerializationCache: true,
      performanceSampleSize: 8,
      skipUnchangedPersistence: false,
    });
    const options = getOptions(manager);

    expect(options.databasePath).toBe('custom.db');
    expect(options.enableCompression).toBe(false);
    expect(options.compressionThreshold).toBe(2048);
    expect(options.defaultTTL).toBe(3600);
    expect(options.gcInterval).toBe(120);
    expect(options.maxVersions).toBe(5);
    expect(options.enableTransactions).toBe(false);
    expect(options.enablePerformanceMetrics).toBe(true);
    expect(options.enableSerializationCache).toBe(true);
    expect(options.performanceSampleSize).toBe(8);
    expect(options.skipUnchangedPersistence).toBe(false);
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

    const storage = getStorage(manager);
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

    const storage = getStorage(manager);
    const entry = storage.get(key);

    expect(entry?.tags).toEqual({});
    expect(entry?.ttl).toBe(getOptions(manager).defaultTTL);
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

    const keyIndex = asInternal(manager).keyIndex;
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

    const keyIndex = asInternal(manager).keyIndex;
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

        expect(asInternal(manager).findKeyByVersion('inventory', 99)).toBeNull();

    await manager.shutdown();
  });

  it('returns null when key index set is empty', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-state-empty-key-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, { databasePath: 'state.db', enableTransactions: false });
    await manager.initialize();

    getKeyIndex(manager).set('inventory', new Set());

    expect(asInternal(manager).findLatestKey('inventory')).toBeNull();

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

        const internal = asInternal(manager);

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
    expect(asInternal(manager).ttlIndex.has(zeroTtlKey)).toBe(false);

    const ttlKey = await manager.saveSSOT('inventory', { id: 'item', stock: 4 }, { ttl: 90 });
    const ttlIndex = asInternal(manager).ttlIndex;
    const expiry = ttlIndex.get(ttlKey);
    expect(typeof expiry).toBe('number');

    const storage = getStorage(manager);
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

    const internal = asInternal(manager);
    internal.storage.delete(firstKey);

    const latestKey = asInternal(manager).findLatestKey('inventory');
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

    const internal = asInternal(manager);
    const firstEntry = internal.storage.get(firstKey);
    const secondEntry = internal.storage.get(secondKey);
    if (firstEntry && secondEntry) {
      secondEntry.version = firstEntry.version;
    }

    const latestKey = asInternal(manager).findLatestKey('inventory');
    expect(latestKey).toBe(firstKey);

    await manager.shutdown();
  });

  it('lazily initializes on first access and skips redundant reinitialization', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-state-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, { databasePath: 'state.db', enableTransactions: false });
    const initializeSpy = vi.spyOn(asInternal(manager), 'initialize');

    await expect(manager.loadSSOT('inventory')).resolves.toBeNull();
    expect(initializeSpy).toHaveBeenCalledTimes(1);

    initializeSpy.mockRestore();
    const redundantSpy = vi.spyOn(asInternal(manager), 'initialize');

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
    await asInternal(manager).runGarbageCollection();
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

    await asInternal(manager).runGarbageCollection();

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
    const internal = asInternal(manager);
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
    const storage = getStorage(manager);
    const originalEntry = JSON.parse(JSON.stringify(storage.get(fullKey)));

    const txId = await manager.beginTransaction();
    const calculateChecksum = asInternal(manager).calculateChecksum.bind(manager);
    const updatedEntry = {
      ...storage.get(fullKey),
      data: { id: 'widget', stock: 9 },
      checksum: calculateChecksum({ id: 'widget', stock: 9 }),
    };

    await asInternal(manager).saveInTransaction(txId, fullKey, updatedEntry);
    expect(storage.get(fullKey)?.data).toEqual({ id: 'widget', stock: 9 });

    await manager.rollbackTransaction(txId);

    expect(storage.get(fullKey)?.data).toEqual(originalEntry.data);
    await manager.shutdown();
  });

  it('records transaction operations and skips rollback data for new entries', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-state-new-tx-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, {
      databasePath: 'state.db',
      enableTransactions: true,
    });

    await manager.initialize();

    const txId = await manager.beginTransaction();
    const internal = asInternal(manager);

    const logicalKey = 'fresh-entry';
    const timestamp = new Date().toISOString();
    const data = { id: 'payload', region: 'tx-new' };
    const checksum = internal.calculateChecksum.call(manager, data);

    const entry = {
      id: 'fresh-entry-id',
      logicalKey,
      timestamp,
      version: 1,
      checksum,
      data,
      compressed: false,
      tags: {},
      metadata: {
        size: JSON.stringify(data).length,
        created: timestamp,
        accessed: timestamp,
        source: 'transaction-test',
      },
    };

    const storageKey = `${logicalKey}_${timestamp}`;
    await internal.saveInTransaction(txId, storageKey, entry);

    const context = internal.activeTransactions.get(txId);
    expect(context.rollbackData.size).toBe(0);
    expect(context.operations).toHaveLength(1);
    expect(context.operations[0]).toMatchObject({ type: 'save', key: storageKey });

    await manager.rollbackTransaction(txId);
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

describe('EnhancedStateManager helper behaviour', () => {

  it('round-trips binary payloads through saveSSOT/loadSSOT', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-binary-roundtrip-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, { databasePath: 'state.db', enableTransactions: false });

    const buffer = Buffer.from([0xde, 0xad, 0xbe, 0xef]);
    const arrayBuffer = new ArrayBuffer(4);
    new Uint8Array(arrayBuffer).set([0x00, 0x11, 0x22, 0x33]);
    const dataView = new DataView(arrayBuffer);
    dataView.setUint16(0, 0x1234);
    dataView.setUint16(2, 0xabcd);
    const typed = new Uint16Array([1234, 5678]);
    const sharedBuffer = typeof SharedArrayBuffer !== 'undefined' ? new SharedArrayBuffer(4) : null;
    if (sharedBuffer) {
      new Uint8Array(sharedBuffer).set([0xaa, 0xbb, 0xcc, 0xdd]);
    }

    const payload: Record<string, unknown> = {
      buffer,
      arrayBuffer,
      dataView,
      typed,
    };
    if (sharedBuffer) {
      payload.sharedBuffer = sharedBuffer;
    }

    await manager.saveSSOT('binary-entry', payload);

    const restored = await manager.loadSSOT('binary-entry');
    expect(restored).not.toBeNull();
    expect(restored?.buffer).toBeInstanceOf(Buffer);
    expect((restored?.buffer as Buffer).equals(buffer)).toBe(true);
    expect(restored?.arrayBuffer).toBeInstanceOf(ArrayBuffer);
    expect(Array.from(new Uint8Array(restored?.arrayBuffer as ArrayBuffer))).toEqual(Array.from(new Uint8Array(arrayBuffer)));
    expect(restored?.dataView).toBeInstanceOf(DataView);
    const revivedView = restored?.dataView as DataView;
    expect(revivedView.getUint16(0)).toBe(0x1234);
    expect(revivedView.getUint16(2)).toBe(0xabcd);
    expect(restored?.typed).toBeInstanceOf(Uint16Array);
    expect(Array.from(restored?.typed as Uint16Array)).toEqual(Array.from(typed));
    if (sharedBuffer) {
      expect(restored?.sharedBuffer).toBeInstanceOf(SharedArrayBuffer);
      expect(Array.from(new Uint8Array(restored?.sharedBuffer as SharedArrayBuffer))).toEqual([0xaa, 0xbb, 0xcc, 0xdd]);
    } else {
      expect(restored?.sharedBuffer).toBeUndefined();
    }

    await manager.shutdown();
  });


  it('encodes binary payloads with special markers during stringify', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-binary-stringify-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, { databasePath: 'state.db', enablePerformanceMetrics: true, enableSerializationCache: false });
    const internal = asInternal(manager);

    const buffer = Buffer.from([0xde, 0xad, 0xbe, 0xef]);
    const arrayBuffer = new ArrayBuffer(4);
    new Uint8Array(arrayBuffer).set([0xff, 0x00, 0x11, 0x22]);
    const dataView = new DataView(arrayBuffer.slice(0));
    dataView.setUint32(0, 0xcafebabe);
    const typed = new Uint32Array([0xc0ffee, 0xdeadbeef]);
    const shared = typeof SharedArrayBuffer !== 'undefined' ? new SharedArrayBuffer(4) : null;
    if (shared) {
      new Uint8Array(shared).set([1, 2, 3, 4]);
    }

    const payload: Record<string, unknown> = {
      buffer,
      arrayBuffer,
      dataView,
      typed,
    };
    if (shared) {
      payload.shared = shared;
    }

    const serialized = internal.stringifyForStorage(payload, 'binary-stringify');
    const parsed = JSON.parse(serialized);

    expect(parsed.buffer).toEqual({ type: 'Buffer', data: Array.from(buffer.values()) });
    expect(parsed.arrayBuffer).toEqual({ __ae_type: 'ArrayBuffer', bytes: [0xff, 0x00, 0x11, 0x22] });
    expect(parsed.dataView).toEqual({ __ae_type: 'DataView', bytes: Array.from(new Uint8Array(dataView.buffer)) });
    expect(parsed.typed).toEqual({ __ae_type: 'TypedArray', name: 'Uint32Array', values: Array.from(typed) });
    if (shared) {
      expect(parsed.shared).toEqual({ __ae_type: 'SharedArrayBuffer', bytes: [1, 2, 3, 4] });
    } else {
      expect(parsed.shared).toBeUndefined();
    }

    await manager.shutdown();
  });

  it('preserves buffer instances when importing compressed entries', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-import-buffer-instance-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, { databasePath: 'state.db', enableTransactions: false });
    const timestamp = new Date().toISOString();
    const buffer = Buffer.from([1, 2, 3]);

    const entry = buildStateEntry('buffer-entry', buffer, {
      timestamp,
      version: 1,
      compressed: true,
      metadata: {
        created: timestamp,
        accessed: timestamp,
        source: 'legacy-import',
        size: buffer.length,
      },
    });

    const exported = buildExportedState(manager, {
      metadata: { version: '1.0.0', timestamp },
      entries: [entry],
      indices: {
        keyIndex: { 'buffer-entry': [`buffer-entry_${timestamp}`] },
        versionIndex: { 'buffer-entry': 1 },
      },
    });

    await manager.importState(exported);

    const storage = getStorage(manager);
    const stored = storage.get(`buffer-entry_${timestamp}`);
    expect(stored?.data).toBeInstanceOf(Buffer);
    expect((stored?.data as Buffer).equals(buffer)).toBe(true);

    await manager.shutdown();
  });

  it('computes deterministic checksums via internal helper', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-checksum-helper-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, { databasePath: 'state.db', enableTransactions: false });
    const internal = asInternal(manager);
    const payload = { id: 'checksum', nested: { value: 42 } };

    const checksum = internal.calculateChecksum(payload);
    const expected = createHash('sha256').update(JSON.stringify(payload)).digest('hex');

    expect(checksum).toBe(expected);
    expect(checksum).toHaveLength(64);

    await manager.shutdown();
  });

  it('retains provided metadata, tags, and checksum during importState', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-import-retain-metadata-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, { databasePath: 'state.db', enableTransactions: false });
    const timestamp = new Date().toISOString();
    const payload = { id: 'retained', state: 'active' };

    const entry: Partial<StateEntry> = {
      id: 'custom-entry',
      logicalKey: 'inventory',
      timestamp,
      version: 4,
      data: payload,
      compressed: false,
      tags: { team: 'alpha', env: 'test' },
      metadata: {
        size: JSON.stringify(payload).length,
        created: timestamp,
        accessed: timestamp,
        source: 'import-test',
        phase: 'beta',
      },
    };

    const exported = buildExportedState(manager, {
      metadata: { version: '1.0.0', timestamp },
      entries: [entry as StateEntry],
      indices: {
        keyIndex: { inventory: [`inventory_${timestamp}`] },
        versionIndex: { inventory: 4 },
      },
    });

    await manager.importState(exported);

    const storage = getStorage(manager);
    const stored = storage.get(`inventory_${timestamp}`);
    const expectedChecksum = createHash('sha256').update(JSON.stringify(payload)).digest('hex');

    expect(stored?.id).toBe('custom-entry');
    expect(stored?.checksum).toBe(expectedChecksum);
    expect(stored?.metadata?.source).toBe('import-test');
    expect(stored?.metadata?.phase).toBe('beta');
    expect(stored?.tags).toEqual({ team: 'alpha', env: 'test' });

    await manager.shutdown();
  });

  it('preserves malformed buffer metadata objects during importState', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-import-malformed-buffer-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, { databasePath: 'state.db', enableTransactions: false });
    const timestamp = new Date().toISOString();

    const malformed = { type: 'Buffer', data: { nested: true } };
    const entry = buildStateEntry('malformed-buffer', malformed, {
      timestamp,
      version: 1,
      compressed: true,
      metadata: {
        created: timestamp,
        accessed: timestamp,
        source: 'legacy-import',
        size: 0,
      },
      checksum: '',
    });

    const exported = buildExportedState(manager, {
      metadata: { version: '1.0.0', timestamp },
      entries: [entry],
      indices: {
        keyIndex: { 'malformed-buffer': [`malformed-buffer_${timestamp}`] },
        versionIndex: { 'malformed-buffer': 1 },
      },
    });

    await manager.importState(exported);

    const storage = getStorage(manager);
    const stored = storage.get(`malformed-buffer_${timestamp}`);
    expect(Buffer.isBuffer(stored?.data)).toBe(false);
    expect(stored?.data).toEqual(malformed);

    await manager.shutdown();
  });

  it('revives numeric arrays into buffers and preserves invalid arrays as-is via importState', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-revive-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, { databasePath: 'state.db', enableTransactions: false });
    const timestamp = new Date().toISOString();
    const numericArray = [72, 73, 74];
    const invalidArray: Array<number | string> = [80, 'not-a-number', 82];

    const numericKey = `legacy-buffer_${timestamp}`;
    const invalidKey = `legacy-invalid_${timestamp}`;

    const exported = buildExportedState(manager, {
      metadata: { version: '1.0.0', timestamp },
      entries: [
        buildStateEntry('legacy-buffer', numericArray, {
          timestamp,
          version: 1,
          compressed: true,
          metadata: {
            source: 'legacy-import',
            size: numericArray.length,
            created: timestamp,
            accessed: timestamp,
          },
        }),
        buildStateEntry('legacy-invalid', invalidArray, {
          timestamp,
          version: 1,
          compressed: true,
          metadata: {
            source: 'legacy-import',
            size: invalidArray.length,
            created: timestamp,
            accessed: timestamp,
          },
        }),
      ],
      indices: {
        keyIndex: {
          'legacy-buffer': [numericKey],
          'legacy-invalid': [invalidKey],
        },
        versionIndex: {
          'legacy-buffer': 1,
          'legacy-invalid': 1,
        },
      },
    });
    await manager.importState(exported);

    const storage = getStorage(manager);
    const numericEntry = storage.get(numericKey);
    expect(Buffer.isBuffer(numericEntry?.data)).toBe(true);
    expect((numericEntry?.data as Buffer).equals(Buffer.from(numericArray))).toBe(true);

    const invalidEntry = storage.get(invalidKey);
    expect(Buffer.isBuffer(invalidEntry?.data)).toBe(false);
    expect(invalidEntry?.data).toEqual(invalidArray);

    await manager.shutdown();
  });

  it('revives additional typed array views from serialized export data', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-typed-array-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, { databasePath: 'state.db', enableTransactions: false });

    const shared = new SharedArrayBuffer(4);
    new Uint8Array(shared).set([1, 2, 3, 4]);

    const buffer = new ArrayBuffer(8);
    const dataView = new DataView(buffer);
    dataView.setUint16(0, 0x1234);
    dataView.setUint32(2, 0xdeadbeef);

    const floatArray = new Float32Array([Math.PI, Math.E]);

    const sharedEntry = buildStateEntry('shared-array-buffer', shared, { version: 1 });
    const dataViewEntry = buildStateEntry('data-view-entry', dataView, { version: 1 });
    const floatEntry = buildStateEntry('float-array-entry', floatArray, { version: 1 });

    const exported = buildExportedState(manager, {
      entries: [sharedEntry, dataViewEntry, floatEntry],
      indices: {
        keyIndex: {
          'shared-array-buffer': [`${sharedEntry.logicalKey}_${sharedEntry.timestamp}`],
          'data-view-entry': [`${dataViewEntry.logicalKey}_${dataViewEntry.timestamp}`],
          'float-array-entry': [`${floatEntry.logicalKey}_${floatEntry.timestamp}`],
        },
        versionIndex: {
          'shared-array-buffer': 1,
          'data-view-entry': 1,
          'float-array-entry': 1,
        },
      },
    });

    const serialized = asInternal(manager).stringifyForStorage(exported, 'typedArrayTest');
    const revived = JSON.parse(serialized);

    await manager.importState(revived);

    const storage = getStorage(manager);
    const sharedKey = `${sharedEntry.logicalKey}_${sharedEntry.timestamp}`;
    const dataViewKey = `${dataViewEntry.logicalKey}_${dataViewEntry.timestamp}`;
    const floatKey = `${floatEntry.logicalKey}_${floatEntry.timestamp}`;

    const storedShared = storage.get(sharedKey);
    expect(storedShared?.data).toBeInstanceOf(SharedArrayBuffer);
    expect(Array.from(new Uint8Array(storedShared?.data as SharedArrayBuffer))).toEqual([1, 2, 3, 4]);

    const storedView = storage.get(dataViewKey);
    expect(storedView?.data).toBeInstanceOf(DataView);
    const revivedView = storedView?.data as DataView;
    expect(revivedView.getUint16(0)).toBe(0x1234);
    expect(revivedView.getUint32(2)).toBe(0xdeadbeef);

    const storedFloat = storage.get(floatKey);
    expect(storedFloat?.data).toBeInstanceOf(Float32Array);
    expect(Array.from(storedFloat?.data as Float32Array)).toEqual(Array.from(floatArray));

    await manager.shutdown();
  });

  it('reconciles versionIndex using entry versions during importState', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-version-index-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, { databasePath: 'state.db', enableTransactions: false });

    const timestamp = new Date().toISOString();
    const entry = buildStateEntry('orders', { id: 'v3-order' }, {
      timestamp,
      version: 3,
      metadata: {
        created: timestamp,
        accessed: timestamp,
        source: 'import-test',
        size: 0,
      },
    });

    const exported = buildExportedState(manager, {
      entries: [entry],
      indices: {
        keyIndex: {
          orders: [`orders_${timestamp}`],
        },
        versionIndex: {
          orders: 1, // stale version that should be reconciled
        },
      },
    });

    await manager.importState(exported);

    const versionIndex = getVersionIndex(manager);
    expect(versionIndex.get('orders')).toBe(3);

    const storage = getStorage(manager);
    const stored = storage.get(`orders_${timestamp}`);
    expect(stored?.version).toBe(3);

    await manager.shutdown();
  });

  it('records zero metadata size when imported data cannot be stringified', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-circular-size-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, { databasePath: 'state.db', enableTransactions: false });
    await manager.initialize();

    const circular: any = { foo: 'bar' };
    circular.self = circular;
    const timestamp = new Date().toISOString();

    const exported = buildExportedState(manager, {
      metadata: { version: '1.0.0', timestamp },
      entries: [
        buildStateEntry('circular-entry', circular, {
          timestamp,
          version: 1,
          metadata: {
            source: 'legacy-import',
            created: timestamp,
            accessed: timestamp,
          },
          checksum: '',
          compressed: false,
        }),
      ],
      indices: {
        keyIndex: { 'circular-entry': [`circular-entry_${timestamp}`] },
        versionIndex: { 'circular-entry': 1 },
      },
    });

    await manager.importState(exported);
    const stored = getStorage(manager).get(`circular-entry_${timestamp}`);
    expect(stored?.metadata.size).toBe(0);
  });

  it('creates snapshots scoped by phase or entity filters', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-snapshot-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, { databasePath: 'state.db', enableTransactions: false });
    await manager.saveSSOT('alpha.orders', { id: 'order-a' }, { phase: 'alpha', tags: { scope: 'orders' } });
    const betaKey = await manager.saveSSOT('beta.inventory', { id: 'stock-beta' }, { phase: 'beta', tags: { scope: 'inventory' } });
    const betaEntityKey = await manager.saveSSOT('gamma.inventory', { id: 'stock-gamma' }, { phase: 'gamma', tags: { scope: 'inventory' } });

    const snapshotSpy = vi.fn();
    manager.on('snapshotCreated', snapshotSpy);

    const snapshotId = await manager.createSnapshot('beta', ['inventory']);
    expect(typeof snapshotId).toBe('string');
    expect(snapshotSpy).toHaveBeenCalledWith(
      expect.objectContaining({
        snapshotId,
        metadata: expect.objectContaining({
          phase: 'beta',
          entities: ['inventory'],
        }),
      })
    );

    const snapshot = await manager.loadSnapshot(snapshotId);
    expect(snapshot).not.toBeNull();
    const snapshotKeys = Object.keys(snapshot as Record<string, unknown>);
    expect(snapshotKeys).toEqual(expect.arrayContaining([betaKey, betaEntityKey]));
    expect(snapshotKeys.some((key) => key.startsWith('alpha.orders'))).toBe(false);

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

    const storage = getStorage(manager);
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

    const storage = getStorage(manager);
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
    const storage = getStorage(manager);
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

    await manager.saveSSOT('inventory', { id: 'widget-1', stock: 5 }, { phase: 'demo-phase' });
    const snapshotId = await manager.createSnapshot('demo-phase', ['inventory']);

    expect(createdSpy).toHaveBeenCalledWith(
      expect.objectContaining({
        snapshotId,
        metadata: expect.objectContaining({
          phase: 'demo-phase',
          entities: ['inventory'],
          ttl: getOptions(manager).defaultTTL * 2,
        }),
      })
    );

    const snapshot = await manager.loadSnapshot(snapshotId);
    expect(snapshot).not.toBeNull();
    const keys = snapshot ? Object.keys(snapshot) : [];
    expect(keys.some(key => key.includes('inventory'))).toBe(true);

    const storage = getStorage(manager);
    const entry = storage.get(snapshotId);
    expect(entry?.logicalKey).toBe('snapshot_demo-phase');
    expect(entry?.ttl).toBe(getOptions(manager).defaultTTL * 2);
    expect(entry?.tags).toEqual({ type: 'snapshot', phase: 'demo-phase' });
    expect(entry?.metadata?.source).toBe('snapshot_manager');
    expect(entry?.metadata?.phase).toBe('demo-phase');
    expect(entry?.metadata?.accessed).toEqual(entry?.metadata?.created);

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

    const storage = getStorage(manager);
    const persistedKey = persistedSpy.mock.calls[0][0].key;
    const entry = storage.get(persistedKey);
    expect(entry?.data).toEqual(artifact);
    expect(entry?.metadata?.source).toBe('failure_handler');
    expect(entry?.ttl).toBe(getOptions(manager).defaultTTL);
    expect(entry?.tags).toEqual({
      type: 'failure',
      phase: 'verification',
      severity: 'medium',
      retryable: 'true',
    });

    warnSpy.mockRestore();
    await manager.shutdown();
  });
});

describe('EnhancedStateManager performance metrics', () => {
  it('collects stringify metrics and cache hits when enabled', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-perf-metrics-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, {
      databasePath: 'state.db',
      enableTransactions: false,
      enablePerformanceMetrics: true,
      enableSerializationCache: true,
      performanceSampleSize: 10,
    });

    await manager.initialize();
    manager.resetPerformanceMetrics();

    const payload = { id: 'metrics', nested: { foo: 'bar' } };
    await manager.saveSSOT('metrics.entry', payload);
    await manager.saveSSOT('metrics.entry.clone', payload);

    const metrics = manager.getPerformanceMetrics();
    expect(metrics.stringifyCalls).toBeGreaterThanOrEqual(2);
    expect(metrics.samples.length).toBeGreaterThan(0);
    expect(metrics.stringifyCacheHits).toBeGreaterThanOrEqual(1);
    await manager.shutdown();
  });

  it('skips persistence writes when state checksum is unchanged', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-persist-metrics-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, {
      databasePath: 'state.db',
      enableTransactions: false,
      enablePerformanceMetrics: true,
    });

    await manager.initialize();
    await manager.saveSSOT('persist.sample', { id: 'persist' });

    const internal = asInternal(manager);
    await internal.persistToDisk();

    const firstMetrics = manager.getPerformanceMetrics();
    expect(firstMetrics.persistedWrites).toBeGreaterThanOrEqual(1);

    await internal.persistToDisk();
    const secondMetrics = manager.getPerformanceMetrics();
    expect(secondMetrics.skippedPersistWrites).toBeGreaterThanOrEqual(1);

    await manager.shutdown();
  });
});


describe('EnhancedStateManager persistence and shutdown', () => {
  it('flushes state and rolls back transactions during shutdown', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-shutdown-rollbacks-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, { databasePath: 'state.db' });
    await manager.initialize();

    const stopSpy = vi.spyOn(manager, 'stopGarbageCollection');
    const persistSpy = vi.spyOn(asInternal(manager), 'persistToDisk').mockResolvedValue();
    const rollbackSpy = vi.spyOn(manager, 'rollbackTransaction');
    const shutdownSpy = vi.fn();
    manager.on('stateManagerShutdown', shutdownSpy);

    const txId = await manager.beginTransaction();
    await manager.saveSSOT('orders', { id: 'txn-order' }, { transactionId: txId });

    await manager.shutdown();

    expect(stopSpy).toHaveBeenCalled();
    expect(persistSpy).toHaveBeenCalled();
    expect(rollbackSpy).toHaveBeenCalledWith(txId);
    expect(shutdownSpy).toHaveBeenCalledTimes(1);

    persistSpy.mockRestore();
    stopSpy.mockRestore();
    rollbackSpy.mockRestore();
  });

  it('propagates persistToDisk failures and logs the error', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-persist-error-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, { databasePath: 'state.db' });
    await manager.initialize();

    const error = new Error('disk full');
    const exportSpy = vi.spyOn(manager, 'exportState').mockRejectedValueOnce(error);
    const errorSpy = vi.spyOn(console, 'error').mockImplementation(() => {});

    await expect(asInternal(manager).persistToDisk()).rejects.toThrow(error);
    expect(errorSpy).toHaveBeenCalledWith('Failed to persist state to disk:', error);

    exportSpy.mockRestore();
    errorSpy.mockRestore();
    await manager.shutdown();
  });

  it('logs loaded entry count when metadata block is missing', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-persistence-log-'));
    tempRoots.push(root);

    const timestamp = new Date().toISOString();
    const fullKey = `inventory_${timestamp}`;
    const persistence = {
      version: '1.0.0',
      entries: [
        buildStateEntry('inventory', { id: 'legacy', stock: 4 }, {
          timestamp,
          version: 2,
          compressed: false,
          checksum: 'legacy-checksum',
          metadata: {
            size: JSON.stringify({ id: 'legacy', stock: 4 }).length,
            created: timestamp,
            accessed: timestamp,
            source: 'persistence-log-test',
          },
        }),
      ],
      indices: {
        keyIndex: { inventory: [fullKey] },
        versionIndex: { inventory: 2 },
      },
    };

    await writeFile(join(root, 'state.db'), JSON.stringify(persistence));

    const logSpy = vi.spyOn(console, 'log').mockImplementation(() => {});
    const manager = new EnhancedStateManager(root, { databasePath: 'state.db', enableTransactions: false });

    await manager.initialize();

    expect(logSpy).toHaveBeenCalledWith(
      expect.stringMatching(/📁 Loaded 1 entries from persistence/),
    );
    expect(await manager.loadSSOT('inventory', 2)).toEqual({ id: 'legacy', stock: 4 });

    logSpy.mockRestore();
    await manager.shutdown();
  });

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
    await asInternal(manager).persistToDisk();

    const databaseFile = asInternal(manager).databaseFile;
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
    await asInternal(manager).persistToDisk();
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

  it('revives legacy buffer payloads during import', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-import-legacy-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, { databasePath: 'state.db' });
    await manager.initialize();

    const timestamp = '2024-03-03T00:00:00.000Z';
    const legacyEntry = {
      logicalKey: 'legacy-buffer',
      timestamp,
      version: 2,
      compressed: true,
      data: { type: 'Buffer', data: [65, 66, 67] },
      metadata: {
        source: 'legacy-import',
        created: timestamp,
        accessed: timestamp,
      },
    } satisfies Partial<StateEntry>;

    const exported = buildExportedState(manager, {
      metadata: { version: '1.0.0', timestamp },
      entries: [legacyEntry as unknown as StateEntry],
      indices: {
        keyIndex: { 'legacy-buffer': [`legacy-buffer_${timestamp}`] },
        versionIndex: { 'legacy-buffer': 2 },
      },
    });

    await manager.importState(exported);

    const storage = getStorage(manager);
    const entry = storage.get(`legacy-buffer_${timestamp}`);
    expect(entry?.compressed).toBe(true);
    expect(Buffer.isBuffer(entry?.data)).toBe(true);
    expect(entry?.metadata?.size).toBe((entry?.data as Buffer).length);

    await manager.shutdown();
  });

  it('recomputes checksum and metadata when importing compressed entries without checksum', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-import-checksum-'));
    tempRoots.push(root);

    const manager = new EnhancedStateManager(root, {
      databasePath: 'state.db',
      enableCompression: true,
      compressionThreshold: 16,
    });
    await manager.initialize();

    const payload = { id: 'bulk', items: ['widget-1', 'widget-2'], note: 'inventory snapshot' };
    const rawJson = JSON.stringify(payload);
    const compressedBuffer = gzipSync(Buffer.from(rawJson, 'utf8'));
    const timestamp = new Date().toISOString();

    const bulkEntry = {
      logicalKey: 'bulk-entry',
      timestamp,
      version: 3,
      compressed: true,
      data: { type: 'Buffer', data: Array.from(compressedBuffer) },
      metadata: {
        created: timestamp,
        accessed: timestamp,
      },
    } satisfies Partial<StateEntry>;

    const exported = buildExportedState(manager, {
      metadata: { version: '1.0.0', timestamp },
      entries: [bulkEntry as unknown as StateEntry],
      indices: {
        keyIndex: { 'bulk-entry': [`bulk-entry_${timestamp}`] },
        versionIndex: { 'bulk-entry': 3 },
      },
    });

    const importedSpy = vi.fn();
    manager.on('stateImported', importedSpy);

    await manager.importState(exported);

    expect(importedSpy).toHaveBeenCalledWith({ entryCount: 1 });
    const restored = await manager.loadSSOT('bulk-entry');
    expect(restored).toEqual(payload);

    await manager.shutdown();
  });

  it('revives compressed buffer entries when importing legacy backups', async () => {
    const exportRoot = await mkdtemp(join(tmpdir(), 'ae-framework-state-export-'));
    const importRoot = await mkdtemp(join(tmpdir(), 'ae-framework-state-import-'));
    tempRoots.push(exportRoot, importRoot);

    const originalManager = new EnhancedStateManager(exportRoot, {
      databasePath: 'state.db',
      enableTransactions: false,
      enableCompression: true,
      compressionThreshold: 1,
    });

    const payload = { id: 'compressed', instructions: 'X'.repeat(512) };
    await originalManager.saveSSOT('inventory', payload, { source: 'legacy-backup' });
    const exportedState = await originalManager.exportState();
    await originalManager.shutdown();

    const sourceEntry = exportedState.entries[0];
    const importManager = new EnhancedStateManager(importRoot, { databasePath: 'state.db', enableTransactions: false });
    const importedSpy = vi.fn();
    importManager.on('stateImported', importedSpy);

    const importState = buildExportedState(importManager, {
      metadata: exportedState.metadata,
      entries: [
        {
          logicalKey: sourceEntry.logicalKey,
          timestamp: sourceEntry.timestamp,
          version: sourceEntry.version,
          compressed: sourceEntry.compressed,
          data: sourceEntry.data,
        } as unknown as StateEntry,
      ],
      indices: exportedState.indices,
    });

    await importManager.importState(importState);

    expect(importedSpy).toHaveBeenCalledWith({ entryCount: 1 });
    const restored = await importManager.loadSSOT('inventory');
    expect(restored).toEqual(payload);

    await importManager.shutdown();
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

    const ttlIndex = asInternal(manager).ttlIndex;
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

    const ttlIndex = asInternal(manager).ttlIndex;
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

describe('EnhancedStateManager garbage collection logging', () => {
  it('logs removal count when expired entries are collected', async () => {
    vi.useFakeTimers();
    const baseTime = new Date('2025-01-01T00:00:00.000Z');
    vi.setSystemTime(baseTime);

    const root = await mkdtemp(join(tmpdir(), 'ae-framework-gc-'));
    tempRoots.push(root);

    const logSpy = vi.spyOn(console, 'log').mockImplementation(() => {});
    const manager = new EnhancedStateManager(root, {
      databasePath: 'state.db',
      enableTransactions: false,
      gcInterval: 3600,
    });

    try {
      await manager.initialize();
      manager.stopGarbageCollection();
      logSpy.mockClear();

      await manager.saveSSOT('session', { id: 'stale' }, { ttl: 1, source: 'gc-test' });
      vi.advanceTimersByTime(2000);

      await manager.collectGarbage();

      expect(logSpy).toHaveBeenCalledWith(
        expect.stringMatching(/removed\s+1\s+expired\s+entr(?:y|ies)/)
      );
      await expect(manager.loadSSOT('session')).resolves.toBeNull();
    } finally {
      logSpy.mockRestore();
      await manager.shutdown();
      vi.useRealTimers();
    }
  });

  it('does not log when no entries expire during collection', async () => {
    vi.useFakeTimers();
    const baseTime = new Date('2025-01-01T12:00:00.000Z');
    vi.setSystemTime(baseTime);

    const root = await mkdtemp(join(tmpdir(), 'ae-framework-gc-clean-'));
    tempRoots.push(root);

    const logSpy = vi.spyOn(console, 'log').mockImplementation(() => {});
    const manager = new EnhancedStateManager(root, {
      databasePath: 'state.db',
      enableTransactions: false,
      gcInterval: 3600,
    });

    try {
      await manager.initialize();
      manager.stopGarbageCollection();
      logSpy.mockClear();

      await manager.collectGarbage();

      expect(logSpy).not.toHaveBeenCalled();
    } finally {
      logSpy.mockRestore();
      await manager.shutdown();
      vi.useRealTimers();
    }
  });
});
