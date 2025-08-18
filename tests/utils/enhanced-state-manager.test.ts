import { describe, it, expect, beforeEach, afterEach, vi } from 'vitest';
import * as fs from 'fs/promises';
import * as path from 'path';
import { EnhancedStateManager, FailureArtifact } from '../../src/utils/enhanced-state-manager.js';
import { AEIR } from '@ae-framework/spec-compiler';

describe('EnhancedStateManager', () => {
  let stateManager: EnhancedStateManager;
  let testDataDir: string;
  
  const mockAEIR: AEIR = {
    version: '1.0.0',
    metadata: {
      name: 'test-spec',
      description: 'Test specification',
      created: '2025-01-20T10:00:00Z',
      updated: '2025-01-20T10:00:00Z'
    },
    glossary: [
      { term: 'User', definition: 'A person who uses the system' }
    ],
    domain: [
      {
        name: 'User',
        description: 'User entity',
        fields: [
          { name: 'id', type: 'string', required: true },
          { name: 'email', type: 'string', required: true }
        ]
      }
    ],
    invariants: [],
    usecases: [],
    api: []
  };

  beforeEach(async () => {
    // Create temporary test directory
    testDataDir = path.join(process.cwd(), 'test-enhanced-state');
    await fs.mkdir(testDataDir, { recursive: true });
    
    // Initialize state manager with test directory
    stateManager = new EnhancedStateManager(testDataDir, {
      enableCompression: true,
      compressionThreshold: 100,
      defaultTTL: 3600, // 1 hour for tests
      gcInterval: 10, // 10 seconds for tests
      maxVersions: 5,
      enableTransactions: true
    });

    await stateManager.initialize();
  });

  afterEach(async () => {
    // Cleanup
    await stateManager.shutdown();
    
    try {
      await fs.rm(testDataDir, { recursive: true, force: true });
    } catch (error) {
      // Ignore cleanup errors
    }
  });

  describe('SSOT Management', () => {
    it('should save and load SSOT data', async () => {
      const logicalKey = 'test-spec';
      
      // Save SSOT
      const savedKey = await stateManager.saveSSOT(logicalKey, mockAEIR, {
        phase: 'test',
        tags: { environment: 'test' },
        source: 'unit-test'
      });
      
      expect(savedKey).toContain(logicalKey);
      expect(savedKey).toContain('T'); // ISO timestamp
      
      // Load SSOT
      const loadedData = await stateManager.loadSSOT(logicalKey);
      expect(loadedData).toEqual(mockAEIR);
    });

    it('should handle versioning correctly', async () => {
      const logicalKey = 'versioned-spec';
      
      // Save multiple versions
      const key1 = await stateManager.saveSSOT(logicalKey, mockAEIR);
      
      // Modify data for second version
      const modifiedAEIR = { 
        ...mockAEIR, 
        metadata: { ...mockAEIR.metadata, description: 'Modified description' }
      };
      
      const key2 = await stateManager.saveSSOT(logicalKey, modifiedAEIR);
      
      expect(key1).not.toBe(key2);
      
      // Get versions
      const versions = await stateManager.getVersions(logicalKey);
      expect(versions).toHaveLength(2);
      expect(versions[0].version).toBe(2); // Latest first
      expect(versions[1].version).toBe(1);
      
      // Load specific version
      const version1Data = await stateManager.loadSSOT(logicalKey, 1);
      expect(version1Data?.metadata.description).toBe('Test specification');
      
      const version2Data = await stateManager.loadSSOT(logicalKey, 2);
      expect(version2Data?.metadata.description).toBe('Modified description');
    });

    it('should handle compression for large data', async () => {
      const logicalKey = 'large-spec';
      
      // Create large AEIR data
      const largeAEIR: AEIR = {
        ...mockAEIR,
        domain: Array(50).fill(0).map((_, i) => ({
          name: `Entity${i}`,
          description: `Large entity ${i}`,
          fields: Array(10).fill(0).map((_, j) => ({
            name: `field${j}`,
            type: 'string',
            required: j % 2 === 0,
            description: `Field ${j} of entity ${i}`
          }))
        }))
      };
      
      const savedKey = await stateManager.saveSSOT(logicalKey, largeAEIR);
      const loadedData = await stateManager.loadSSOT(logicalKey);
      
      expect(loadedData).toEqual(largeAEIR);
      
      // Check that compression was applied
      const stats = stateManager.getStatistics();
      expect(stats.compressedEntries).toBeGreaterThan(0);
    });
  });

  describe('Transaction Management', () => {
    it('should support transaction commit', async () => {
      const logicalKey = 'transaction-test';
      
      const txId = await stateManager.beginTransaction();
      expect(txId).toBeTruthy();
      
      const savedKey = await stateManager.saveSSOT(logicalKey, mockAEIR, {
        phase: 'test',
        transactionId: txId
      });
      
      await stateManager.commitTransaction(txId);
      
      // Data should be available after commit
      const loadedData = await stateManager.loadSSOT(logicalKey);
      expect(loadedData).toEqual(mockAEIR);
    });

    it('should support transaction rollback', async () => {
      const logicalKey = 'rollback-test';
      
      const txId = await stateManager.beginTransaction();
      
      // Save data within the transaction
      const savedKey = await stateManager.saveSSOT(logicalKey, mockAEIR, {
        transactionId: txId
      });
      
      // Data should be available during transaction
      let loadedData = await stateManager.loadSSOT(logicalKey);
      expect(loadedData).toEqual(mockAEIR);
      
      await stateManager.rollbackTransaction(txId);
      
      // Data should not be available after rollback
      loadedData = await stateManager.loadSSOT(logicalKey);
      expect(loadedData).toBeNull();
    });

    it('should handle transaction errors', async () => {
      // Test invalid transaction ID
      await expect(stateManager.commitTransaction('invalid-tx-id'))
        .rejects.toThrow('Transaction not found');
      
      await expect(stateManager.rollbackTransaction('invalid-tx-id'))
        .rejects.toThrow('Transaction not found');
    });
  });

  describe('Snapshot Management', () => {
    it('should create and load snapshots', async () => {
      const phase = 'test-phase';
      
      // Save some data first
      await stateManager.saveSSOT('spec1', mockAEIR, { phase });
      await stateManager.saveSSOT('spec2', mockAEIR, { phase });
      
      // Create snapshot
      const snapshotId = await stateManager.createSnapshot(phase);
      expect(snapshotId).toContain('snapshot');
      expect(snapshotId).toContain(phase);
      
      // Load snapshot
      const snapshot = await stateManager.loadSnapshot(snapshotId);
      expect(snapshot).toBeTruthy();
      expect(Object.keys(snapshot!).length).toBeGreaterThan(0);
    });

    it('should handle entity-specific snapshots', async () => {
      const phase = 'entity-phase';
      const entities = ['User', 'Product'];
      
      // Save data with entity references
      await stateManager.saveSSOT('user-spec', mockAEIR, { phase });
      await stateManager.saveSSOT('product-spec', mockAEIR, { phase });
      await stateManager.saveSSOT('other-spec', mockAEIR, { phase: 'other' });
      
      const snapshotId = await stateManager.createSnapshot(phase, entities);
      const snapshot = await stateManager.loadSnapshot(snapshotId);
      
      expect(snapshot).toBeTruthy();
    });
  });

  describe('Failure Artifact Management', () => {
    it('should persist and emit failure artifacts', async () => {
      const eventPromise = new Promise((resolve) => {
        stateManager.once('failureArtifactPersisted', resolve);
      });
      
      const failureArtifact: FailureArtifact = {
        id: 'test-failure-1',
        timestamp: new Date().toISOString(),
        phase: 'test',
        type: 'validation',
        error: new Error('Test validation failed'),
        context: { testCase: 'unit-test' },
        artifacts: ['failed-spec.json'],
        retryable: true,
        severity: 'medium'
      };
      
      await stateManager.persistFailureArtifact(failureArtifact);
      
      const event = await eventPromise;
      expect(event).toBeTruthy();
      expect((event as any).artifact.id).toBe(failureArtifact.id);
      expect((event as any).cegis_trigger).toBe(true);
    });

    it('should emit specific failure type events', async () => {
      const validationEventPromise = new Promise((resolve) => {
        stateManager.once('failure_validation', resolve);
      });
      
      const failureArtifact: FailureArtifact = {
        id: 'validation-failure',
        timestamp: new Date().toISOString(),
        phase: 'test',
        type: 'validation',
        error: new Error('Validation error'),
        context: {},
        artifacts: [],
        retryable: false,
        severity: 'high'
      };
      
      await stateManager.persistFailureArtifact(failureArtifact);
      
      const event = await validationEventPromise;
      expect(event).toEqual(failureArtifact);
    });
  });

  describe('Statistics and Monitoring', () => {
    it('should provide accurate statistics', async () => {
      // Initially empty
      let stats = stateManager.getStatistics();
      expect(stats.totalEntries).toBe(0);
      
      // Add some data
      await stateManager.saveSSOT('test1', mockAEIR, { phase: 'test' });
      await stateManager.saveSSOT('test2', mockAEIR, { phase: 'test' });
      await stateManager.saveSSOT('test1', mockAEIR, { phase: 'test' }); // Version 2
      
      stats = stateManager.getStatistics();
      expect(stats.totalEntries).toBe(3);
      expect(stats.logicalKeys).toBe(2);
      expect(stats.averageVersions).toBe(1.5);
      expect(stats.oldestEntry).toBeTruthy();
      expect(stats.newestEntry).toBeTruthy();
    });

    it('should track compression statistics', async () => {
      // Create large data that will be compressed
      const largeData = { ...mockAEIR, description: 'x'.repeat(2000) };
      await stateManager.saveSSOT('large', largeData);
      
      const stats = stateManager.getStatistics();
      expect(stats.compressedEntries).toBeGreaterThan(0);
    });
  });

  describe('State Export/Import', () => {
    it('should export and import state correctly', async () => {
      // Add some data
      await stateManager.saveSSOT('export-test', mockAEIR, { 
        phase: 'test',
        tags: { exported: 'true' }
      });
      
      // Export state
      const exportedState = await stateManager.exportState();
      expect(exportedState.entries).toHaveLength(1);
      expect(exportedState.metadata.version).toBe('1.0.0');
      
      // Create new state manager
      const newStateDir = path.join(process.cwd(), 'test-import-state');
      await fs.mkdir(newStateDir, { recursive: true });
      
      const newStateManager = new EnhancedStateManager(newStateDir);
      await newStateManager.initialize();
      
      // Import state
      await newStateManager.importState(exportedState);
      
      // Verify imported data
      const importedData = await newStateManager.loadSSOT('export-test');
      expect(importedData).toEqual(mockAEIR);
      
      // Cleanup
      await newStateManager.shutdown();
      await fs.rm(newStateDir, { recursive: true, force: true });
    });
  });

  describe('Garbage Collection', () => {
    it('should handle TTL expiration', async () => {
      // Save data with very short TTL
      await stateManager.saveSSOT('short-ttl', mockAEIR, { 
        ttl: 1 // 1 second
      });
      
      // Data should be available immediately
      let data = await stateManager.loadSSOT('short-ttl');
      expect(data).toEqual(mockAEIR);
      
      // Wait for TTL to expire and trigger GC
      await new Promise(resolve => setTimeout(resolve, 1500));
      await (stateManager as any).runGarbageCollection();
      
      // Data should be gone after GC
      data = await stateManager.loadSSOT('short-ttl');
      expect(data).toBeNull();
    });

    it('should emit GC events', async () => {
      const gcEventPromise = new Promise((resolve) => {
        stateManager.once('garbageCollectionCompleted', resolve);
      });
      
      // Save data with short TTL
      await stateManager.saveSSOT('gc-test', mockAEIR, { ttl: 1 });
      
      // Wait and trigger GC
      await new Promise(resolve => setTimeout(resolve, 1500));
      await (stateManager as any).runGarbageCollection();
      
      const event = await gcEventPromise;
      expect((event as any).expiredCount).toBeGreaterThan(0);
    });
  });

  describe('Version Cleanup', () => {
    it('should cleanup old versions beyond maxVersions', async () => {
      const logicalKey = 'version-cleanup-test';
      
      // Create more versions than maxVersions (5)
      for (let i = 1; i <= 7; i++) {
        const modifiedAEIR = {
          ...mockAEIR,
          metadata: { ...mockAEIR.metadata, description: `Version ${i}` }
        };
        await stateManager.saveSSOT(logicalKey, modifiedAEIR);
      }
      
      // Should only have maxVersions (5) versions
      const versions = await stateManager.getVersions(logicalKey);
      expect(versions.length).toBe(5);
      
      // Latest version should be kept (newest first)
      expect(versions[0].version).toBe(7);
      
      // Versions should be in descending order (newest to oldest)
      for (let i = 1; i < versions.length; i++) {
        expect(versions[i].version).toBeLessThan(versions[i - 1].version);
      }
    });
  });

  describe('Event System', () => {
    it('should emit state manager lifecycle events', async () => {
      const events: string[] = [];
      
      const newStateDir = path.join(process.cwd(), 'test-events-state');
      await fs.mkdir(newStateDir, { recursive: true });
      
      const eventStateManager = new EnhancedStateManager(newStateDir);
      
      eventStateManager.on('stateManagerInitialized', () => events.push('initialized'));
      eventStateManager.on('ssotSaved', () => events.push('ssotSaved'));
      eventStateManager.on('stateManagerShutdown', () => events.push('shutdown'));
      
      await eventStateManager.initialize();
      await eventStateManager.saveSSOT('event-test', mockAEIR);
      await eventStateManager.shutdown();
      
      expect(events).toContain('initialized');
      expect(events).toContain('ssotSaved');
      expect(events).toContain('shutdown');
      
      // Cleanup
      await fs.rm(newStateDir, { recursive: true, force: true });
    });
  });
});