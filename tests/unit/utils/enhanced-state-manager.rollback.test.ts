import { afterAll, describe, expect, it, vi } from 'vitest';
import { mkdtemp, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { EnhancedStateManager } from '../../../src/utils/enhanced-state-manager.js';

const rollbackTempRoots: string[] = [];

afterAll(async () => {
  await Promise.all(rollbackTempRoots.map((dir) => rm(dir, { recursive: true, force: true })));
});

describe('EnhancedStateManager events & rollback behaviour', () => {
  it('emits stateManagerInitialized only once', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-rollback-init-'));
    rollbackTempRoots.push(root);

    const manager = new EnhancedStateManager(root, { databasePath: 'state.db', enableTransactions: false });
    const initializedSpy = vi.fn();
    manager.on('stateManagerInitialized', initializedSpy);

    await manager.initialize();
    await manager.initialize();

    expect(initializedSpy).toHaveBeenCalledTimes(1);

    await manager.shutdown();
  });

  it('restores previous state on rollback and emits transactionRolledBack', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-rollback-'));
    rollbackTempRoots.push(root);

    const manager = new EnhancedStateManager(root, {
      databasePath: 'state.db',
      enableTransactions: true,
      gcInterval: 3600,
    });

    await manager.saveSSOT('inventory', { id: 'baseline', stock: 10 });

    const rollbackSpy = vi.fn();
    manager.on('transactionRolledBack', rollbackSpy);

    const txId = await manager.beginTransaction();
    await manager.saveSSOT('inventory', { id: 'baseline', stock: 99 }, { transactionId: txId });

    await manager.rollbackTransaction(txId);

    const restored = await manager.loadSSOT('inventory');
    expect(restored).toEqual({ id: 'baseline', stock: 10 });
    expect(rollbackSpy).toHaveBeenCalledWith(expect.objectContaining({ txId, operationCount: expect.any(Number) }));
    expect(manager.getStatistics().activeTransactions).toBe(0);

    await manager.shutdown();
  });

  it('persists failure artifacts with expected TTL, tags, and source metadata', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-rollback-failure-'));
    rollbackTempRoots.push(root);

    const manager = new EnhancedStateManager(root, { databasePath: 'state.db' });
    const persistedSpy = vi.fn();
    const typeSpy = vi.fn();
    const warnSpy = vi.spyOn(console, 'warn').mockImplementation(() => {});
    manager.on('failureArtifactPersisted', persistedSpy);
    manager.on('failure_validation', typeSpy);

    const artifact = {
      id: 'artifact-rollback',
      timestamp: new Date().toISOString(),
      phase: 'operate',
      type: 'validation',
      error: new Error('Schema mismatch'),
      context: { step: 'validate' },
      artifacts: ['report.json'],
      retryable: false,
      severity: 'high' as const,
    };

    await manager.persistFailureArtifact(artifact);

    expect(persistedSpy).toHaveBeenCalledWith(expect.objectContaining({
      artifact,
      key: expect.stringMatching(/failure_operate_/),
      cegis_trigger: true,
    }));
    expect(typeSpy).toHaveBeenCalledWith(artifact);

    const storage = (manager as unknown as { storage: Map<string, any> }).storage;
    const persistedKey = persistedSpy.mock.calls[0][0].key;
    const entry = storage.get(persistedKey);
    expect(entry?.logicalKey).toBe('failure_operate');
    expect(entry?.ttl).toBe((manager as any).options.defaultTTL);
    expect(entry?.tags).toEqual({
      type: 'failure',
      phase: 'operate',
      severity: 'high',
      retryable: 'false',
    });
    expect(entry?.metadata?.source).toBe('failure_handler');

    warnSpy.mockRestore();
    await manager.shutdown();
  });

  it('revives legacy Buffer payloads when importing state', async () => {
    const root = await mkdtemp(join(tmpdir(), 'ae-framework-rollback-import-'));
    rollbackTempRoots.push(root);

    const manager = new EnhancedStateManager(root, { databasePath: 'state.db', enableTransactions: false });

    const timestamp = '2024-03-03T00:00:00.000Z';
    const exported = {
      metadata: { version: '1.0.0' },
      entries: [
        {
          logicalKey: 'legacy-buffer',
          timestamp,
          version: 2,
          compressed: true,
          data: { type: 'Buffer', data: [65, 66, 67] },
          metadata: {},
        },
      ],
      indices: {
        keyIndex: { 'legacy-buffer': [`legacy-buffer_${timestamp}`] },
        versionIndex: { 'legacy-buffer': 2 },
      },
    };

    await manager.importState(exported as any);

    const storage = (manager as unknown as { storage: Map<string, any> }).storage;
    const entry = storage.get(`legacy-buffer_${timestamp}`);
    expect(entry?.compressed).toBe(true);
    expect(Buffer.isBuffer(entry?.data)).toBe(true);
    expect(entry?.metadata?.size).toBe((entry?.data as Buffer).length);

    await manager.shutdown();
  });
});
