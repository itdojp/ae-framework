import * as fs from 'fs/promises';
import * as path from 'path';
import { EventEmitter } from 'events';
import { v4 as uuidv4 } from 'uuid';
import { createHash } from 'crypto';
import { promisify } from 'util';
import { gzip, gunzip } from 'zlib';
import { AEIR } from '@ae-framework/spec-compiler';

const gzipAsync = promisify(gzip);
const gunzipAsync = promisify(gunzip);

/**
 * Enhanced State Storage Entry with versioning and metadata
 */
export interface StateEntry<T = any> {
  id: string;
  logicalKey: string;
  timestamp: string; // ISO format
  version: number;
  checksum: string;
  data: T;
  compressed: boolean;
  tags: Record<string, string>;
  ttl?: number; // TTL in seconds
  metadata: {
    size: number;
    created: string;
    accessed: string;
    source: string;
    phase?: string;
  };
}

/**
 * Storage options for enhanced state management
 */
export interface StorageOptions {
  databasePath?: string;
  enableCompression?: boolean;
  compressionThreshold?: number; // bytes
  defaultTTL?: number; // seconds
  gcInterval?: number; // seconds
  maxVersions?: number;
  enableTransactions?: boolean;
}

/**
 * Failure artifact information for CEGIS integration
 */
export interface FailureArtifact {
  id: string;
  timestamp: string;
  phase: string;
  type: 'validation' | 'compilation' | 'test' | 'verification' | 'generation';
  error: Error;
  context: Record<string, any>;
  artifacts: string[];
  retryable: boolean;
  severity: 'low' | 'medium' | 'high' | 'critical';
}

/**
 * Snapshot metadata for compressed storage
 */
export interface SnapshotMetadata {
  id: string;
  timestamp: string;
  phase: string;
  entities: string[];
  checksum: string;
  compressed: boolean;
  size: number;
  ttl?: number;
}

/**
 * Transaction context for atomic operations
 */
interface TransactionContext {
  id: string;
  operations: Array<{
    type: 'save' | 'delete' | 'update';
    key: string;
    data?: any;
    previousData?: any;
  }>;
  rollbackData: Map<string, StateEntry>;
  committed: boolean;
}

/**
 * Enhanced State Manager with SQLite-like storage, compression, and EventBus integration
 */
export class EnhancedStateManager extends EventEmitter {
  private storage = new Map<string, StateEntry>();
  private keyIndex = new Map<string, Set<string>>(); // logicalKey -> Set of full keys
  private versionIndex = new Map<string, number>(); // logicalKey -> latest version
  private ttlIndex = new Map<string, number>(); // key -> expiry timestamp
  private activeTransactions = new Map<string, TransactionContext>();
  private gcTimer?: NodeJS.Timeout;
  private isInitialized = false;

  private readonly options: Required<StorageOptions>;
  private readonly dataDir: string;
  private readonly databaseFile: string;

  constructor(projectRoot?: string, options: StorageOptions = {}) {
    super();
    
    this.options = {
      databasePath: options.databasePath || '.ae/enhanced-state.db',
      enableCompression: options.enableCompression ?? true,
      compressionThreshold: options.compressionThreshold || 1024, // 1KB
      defaultTTL: options.defaultTTL || 86400 * 7, // 7 days
      gcInterval: options.gcInterval || 3600, // 1 hour
      maxVersions: options.maxVersions || 10,
      enableTransactions: options.enableTransactions ?? true
    };

    const root = projectRoot || process.cwd();
    this.dataDir = path.join(root, '.ae');
    this.databaseFile = path.join(root, this.options.databasePath);
  }

  /**
   * Initialize the enhanced state manager
   */
  async initialize(): Promise<void> {
    if (this.isInitialized) {
      return;
    }

    // Ensure data directory exists
    await fs.mkdir(this.dataDir, { recursive: true });

    // Load existing state from persistence
    await this.loadFromPersistence();

    // Start garbage collection
    this.startGarbageCollection();

    this.isInitialized = true;
    this.emit('stateManagerInitialized');
  }

  /**
   * Save Single Source of Truth (SSOT) data with versioning
   */
  async saveSSOT(logicalKey: string, data: AEIR, options?: {
    phase?: string;
    tags?: Record<string, string>;
    ttl?: number;
    source?: string;
    transactionId?: string; // If provided, use this transaction instead of creating new one
  }): Promise<string> {
    await this.ensureInitialized();

    const timestamp = new Date().toISOString();
    const fullKey = `${logicalKey}_${timestamp}`;
    const version = this.getNextVersion(logicalKey);
    
    const entry: StateEntry<AEIR> = {
      id: uuidv4(),
      logicalKey,
      timestamp,
      version,
      checksum: this.calculateChecksum(data),
      data,
      compressed: false,
      tags: options?.tags || {},
      ttl: options?.ttl || this.options.defaultTTL,
      metadata: {
        size: JSON.stringify(data).length,
        created: timestamp,
        accessed: timestamp,
        source: options?.source || 'unknown',
        phase: options?.phase
      }
    };

    // Apply compression if needed
    if (this.shouldCompress(entry.metadata.size)) {
      entry.data = await this.compress(entry.data);
      entry.compressed = true;
    }

    // Store with transaction if enabled or transaction ID provided
    if (options?.transactionId) {
      // Use existing transaction
      await this.saveInTransaction(options.transactionId, fullKey, entry);
    } else if (this.options.enableTransactions && !options?.transactionId) {
      // Create new transaction
      const txId = await this.beginTransaction();
      try {
        await this.saveInTransaction(txId, fullKey, entry);
        await this.commitTransaction(txId);
      } catch (error) {
        await this.rollbackTransaction(txId);
        throw error;
      }
    } else {
      // No transaction
      await this.saveEntry(fullKey, entry);
      this.updateIndices(logicalKey, fullKey, entry);
    }

    // Clean up old versions
    await this.cleanupOldVersions(logicalKey);

    this.emit('ssotSaved', { logicalKey, fullKey, version, entry });
    return fullKey;
  }

  /**
   * Load SSOT data by logical key (latest version by default)
   */
  async loadSSOT(logicalKey: string, version?: number): Promise<AEIR | null> {
    await this.ensureInitialized();

    const fullKey = version 
      ? this.findKeyByVersion(logicalKey, version)
      : this.findLatestKey(logicalKey);

    if (!fullKey) {
      return null;
    }

    const entry = this.storage.get(fullKey);
    if (!entry) {
      return null;
    }

    // Update access timestamp
    entry.metadata.accessed = new Date().toISOString();

    // Decompress if needed
    let data = entry.data;
    if (entry.compressed) {
      data = await this.decompress(data as Buffer);
    }

    this.emit('ssotLoaded', { logicalKey, fullKey, version: entry.version });
    return data as AEIR;
  }

  /**
   * Create compressed snapshot of current state
   */
  async createSnapshot(phase: string, entities?: string[]): Promise<string> {
    await this.ensureInitialized();

    const timestamp = new Date().toISOString();
    const snapshotId = `snapshot_${phase}_${timestamp}`;
    
    // Collect all relevant entries
    const snapshotData: Record<string, StateEntry> = {};
    
    for (const [key, entry] of this.storage) {
      if (entry.metadata.phase === phase || (entities && entities.some(e => entry.logicalKey.includes(e)))) {
        snapshotData[key] = entry;
      }
    }

    const snapshotMetadata: SnapshotMetadata = {
      id: snapshotId,
      timestamp,
      phase,
      entities: entities || [],
      checksum: this.calculateChecksum(snapshotData),
      compressed: true,
      size: JSON.stringify(snapshotData).length,
      ttl: this.options.defaultTTL * 2 // Longer TTL for snapshots
    };

    // Compress snapshot data
    const compressedData = await this.compress(snapshotData);
    
    // Store snapshot
    const snapshotEntry: StateEntry = {
      id: uuidv4(),
      logicalKey: `snapshot_${phase}`,
      timestamp,
      version: 1,
      checksum: snapshotMetadata.checksum,
      data: compressedData,
      compressed: true,
      tags: { type: 'snapshot', phase },
      ttl: snapshotMetadata.ttl,
      metadata: {
        size: Buffer.byteLength(compressedData as Buffer),
        created: timestamp,
        accessed: timestamp,
        source: 'snapshot_manager',
        phase
      }
    };

    await this.saveEntry(snapshotId, snapshotEntry);
    
    this.emit('snapshotCreated', { snapshotId, metadata: snapshotMetadata });
    return snapshotId;
  }

  /**
   * Load snapshot by ID
   */
  async loadSnapshot(snapshotId: string): Promise<Record<string, StateEntry> | null> {
    await this.ensureInitialized();

    const entry = this.storage.get(snapshotId);
    if (!entry) {
      return null;
    }

    const decompressedData = await this.decompress(entry.data as Buffer);
    this.emit('snapshotLoaded', { snapshotId });
    
    return decompressedData as Record<string, StateEntry>;
  }

  /**
   * Persist failure artifact and notify EventBus for CEGIS integration
   */
  async persistFailureArtifact(artifact: FailureArtifact): Promise<void> {
    await this.ensureInitialized();

    const timestamp = new Date().toISOString();
    const failureKey = `failure_${artifact.phase}_${timestamp}`;
    
    const entry: StateEntry<FailureArtifact> = {
      id: uuidv4(),
      logicalKey: `failure_${artifact.phase}`,
      timestamp,
      version: 1,
      checksum: this.calculateChecksum(artifact),
      data: artifact,
      compressed: false,
      tags: { 
        type: 'failure',
        phase: artifact.phase,
        severity: artifact.severity,
        retryable: artifact.retryable.toString()
      },
      ttl: this.options.defaultTTL,
      metadata: {
        size: JSON.stringify(artifact).length,
        created: timestamp,
        accessed: timestamp,
        source: 'failure_handler',
        phase: artifact.phase
      }
    };

    await this.saveEntry(failureKey, entry);

    // Emit EventBus notification for CEGIS
    this.emit('failureArtifactPersisted', {
      artifact,
      key: failureKey,
      timestamp,
      cegis_trigger: true // Explicit CEGIS trigger
    });

    // Also emit specific failure event based on type
    this.emit(`failure_${artifact.type}`, artifact);
    
    console.warn(`🚨 Failure artifact persisted: ${artifact.type} in ${artifact.phase} (${artifact.severity})`);
  }

  /**
   * Begin transaction for atomic operations
   */
  async beginTransaction(): Promise<string> {
    if (!this.options.enableTransactions) {
      throw new Error('Transactions are disabled');
    }

    const txId = uuidv4();
    const context: TransactionContext = {
      id: txId,
      operations: [],
      rollbackData: new Map(),
      committed: false
    };

    this.activeTransactions.set(txId, context);
    this.emit('transactionStarted', { txId });
    
    return txId;
  }

  /**
   * Commit transaction
   */
  async commitTransaction(txId: string): Promise<void> {
    const context = this.activeTransactions.get(txId);
    if (!context) {
      throw new Error(`Transaction not found: ${txId}`);
    }

    try {
      // All operations were already applied during the transaction
      // Just mark as committed and clean up
      context.committed = true;
      
      // Persist changes to disk
      await this.persistToDisk();
      
      this.activeTransactions.delete(txId);
      this.emit('transactionCommitted', { txId, operationCount: context.operations.length });
      
    } catch (error) {
      // If persist fails, rollback
      await this.rollbackTransaction(txId);
      throw error;
    }
  }

  /**
   * Rollback transaction
   */
  async rollbackTransaction(txId: string): Promise<void> {
    const context = this.activeTransactions.get(txId);
    if (!context) {
      throw new Error(`Transaction not found: ${txId}`);
    }

    // Clear indices first
    this.keyIndex.clear();
    this.versionIndex.clear();
    this.ttlIndex.clear();

    // Remove all keys that were modified in this transaction
    for (const op of context.operations) {
      this.storage.delete(op.key);
    }

    // Restore previous state only for keys that existed before
    for (const [key, previousEntry] of context.rollbackData) {
      if (previousEntry) {
        this.storage.set(key, previousEntry);
      }
      // If previousEntry is undefined, the key didn't exist before, so we leave it deleted
    }

    // Rebuild indices from remaining entries
    for (const [key, entry] of this.storage) {
      this.updateIndices(entry.logicalKey, key, entry);
    }

    this.activeTransactions.delete(txId);
    this.emit('transactionRolledBack', { txId, operationCount: context.operations.length });
  }

  /**
   * Get all versions of a logical key
   */
  async getVersions(logicalKey: string): Promise<Array<{ version: number; timestamp: string; key: string }>> {
    await this.ensureInitialized();

    const keys = this.keyIndex.get(logicalKey);
    if (!keys) {
      return [];
    }

    const versions = Array.from(keys)
      .map(key => {
        const entry = this.storage.get(key);
        return entry ? {
          version: entry.version,
          timestamp: entry.timestamp,
          key
        } : null;
      })
      .filter(Boolean) as Array<{ version: number; timestamp: string; key: string }>;

    return versions.sort((a, b) => b.version - a.version);
  }

  /**
   * Cleanup old versions beyond maxVersions limit
   */
  private async cleanupOldVersions(logicalKey: string): Promise<void> {
    const versions = await this.getVersions(logicalKey);
    
    if (versions.length > this.options.maxVersions) {
      const toDelete = versions.slice(this.options.maxVersions);
      
      for (const versionInfo of toDelete) {
        this.storage.delete(versionInfo.key);
        
        const keys = this.keyIndex.get(logicalKey);
        if (keys) {
          keys.delete(versionInfo.key);
        }
        
        this.ttlIndex.delete(versionInfo.key);
      }
      
      this.emit('versionsCleanedUp', { logicalKey, deletedCount: toDelete.length });
    }
  }

  /**
   * Start garbage collection process
   */
  private startGarbageCollection(): void {
    this.gcTimer = setInterval(() => {
      this.runGarbageCollection();
    }, this.options.gcInterval * 1000);
  }

  /**
   * Run garbage collection to remove expired entries
   */
  private async runGarbageCollection(): Promise<void> {
    const now = Date.now();
    const expiredKeys: string[] = [];

    for (const [key, expiryTime] of this.ttlIndex) {
      if (now >= expiryTime) {
        expiredKeys.push(key);
      }
    }

    for (const key of expiredKeys) {
      const entry = this.storage.get(key);
      if (entry) {
        // Remove from all indices
        this.storage.delete(key);
        this.ttlIndex.delete(key);
        
        const keys = this.keyIndex.get(entry.logicalKey);
        if (keys) {
          keys.delete(key);
          if (keys.size === 0) {
            this.keyIndex.delete(entry.logicalKey);
            this.versionIndex.delete(entry.logicalKey);
          }
        }
      }
    }

    if (expiredKeys.length > 0) {
      this.emit('garbageCollectionCompleted', { expiredCount: expiredKeys.length });
      console.log(`🗑️  Garbage collection: removed ${expiredKeys.length} expired entries`);
    }
  }

  /**
   * Stop garbage collection
   */
  stopGarbageCollection(): void {
    if (this.gcTimer) {
      clearInterval(this.gcTimer);
      this.gcTimer = undefined;
    }
  }

  /**
   * Get storage statistics
   */
  getStatistics(): {
    totalEntries: number;
    totalSize: number;
    compressedEntries: number;
    logicalKeys: number;
    averageVersions: number;
    oldestEntry: string | null;
    newestEntry: string | null;
    activeTransactions: number;
  } {
    const entries = Array.from(this.storage.values());
    const totalSize = entries.reduce((sum, entry) => sum + entry.metadata.size, 0);
    const compressedEntries = entries.filter(e => e.compressed).length;
    
    const timestamps = entries.map(e => e.timestamp).sort();
    
    return {
      totalEntries: this.storage.size,
      totalSize,
      compressedEntries,
      logicalKeys: this.keyIndex.size,
      averageVersions: this.keyIndex.size > 0 ? this.storage.size / this.keyIndex.size : 0,
      oldestEntry: timestamps[0] || null,
      newestEntry: timestamps[timestamps.length - 1] || null,
      activeTransactions: this.activeTransactions.size
    };
  }

  /**
   * Export state for backup or migration
   */
  async exportState(): Promise<{
    metadata: { version: string; timestamp: string; options: StorageOptions };
    entries: StateEntry[];
    indices: {
      keyIndex: Record<string, string[]>;
      versionIndex: Record<string, number>;
    };
  }> {
    await this.ensureInitialized();

    return {
      metadata: {
        version: '1.0.0',
        timestamp: new Date().toISOString(),
        options: this.options
      },
      entries: Array.from(this.storage.values()),
      indices: {
        keyIndex: Object.fromEntries(
          Array.from(this.keyIndex.entries()).map(([k, v]) => [k, Array.from(v)])
        ),
        versionIndex: Object.fromEntries(this.versionIndex)
      }
    };
  }

  /**
   * Import state from backup or migration
   */
  async importState(exportedState: Awaited<ReturnType<typeof this.exportState>>): Promise<void> {
    await this.ensureInitialized();

    // Clear current state
    this.storage.clear();
    this.keyIndex.clear();
    this.versionIndex.clear();
    this.ttlIndex.clear();

    // Import entries
    for (const entry of exportedState.entries) {
      const fullKey = `${entry.logicalKey}_${entry.timestamp}`;
      this.storage.set(fullKey, entry);
      
      // Update TTL index
      if (entry.ttl) {
        const expiryTime = new Date(entry.timestamp).getTime() + (entry.ttl * 1000);
        this.ttlIndex.set(fullKey, expiryTime);
      }
    }

    // Import indices
    for (const [logicalKey, keys] of Object.entries(exportedState.indices.keyIndex)) {
      this.keyIndex.set(logicalKey, new Set(keys));
    }

    for (const [logicalKey, version] of Object.entries(exportedState.indices.versionIndex)) {
      this.versionIndex.set(logicalKey, version);
    }

    this.emit('stateImported', { entryCount: exportedState.entries.length });
  }

  // Private helper methods

  private async ensureInitialized(): Promise<void> {
    if (!this.isInitialized) {
      await this.initialize();
    }
  }

  private getNextVersion(logicalKey: string): number {
    const currentVersion = this.versionIndex.get(logicalKey) || 0;
    const nextVersion = currentVersion + 1;
    this.versionIndex.set(logicalKey, nextVersion);
    return nextVersion;
  }

  private findLatestKey(logicalKey: string): string | null {
    const keys = this.keyIndex.get(logicalKey);
    if (!keys || keys.size === 0) {
      return null;
    }

    // Find the key with the latest version
    let latestKey: string | null = null;
    let latestVersion = -1;

    for (const key of keys) {
      const entry = this.storage.get(key);
      if (entry && entry.version > latestVersion) {
        latestVersion = entry.version;
        latestKey = key;
      }
    }

    return latestKey;
  }

  private findKeyByVersion(logicalKey: string, version: number): string | null {
    const keys = this.keyIndex.get(logicalKey);
    if (!keys) {
      return null;
    }

    for (const key of keys) {
      const entry = this.storage.get(key);
      if (entry && entry.version === version) {
        return key;
      }
    }

    return null;
  }

  private updateIndices(logicalKey: string, fullKey: string, entry: StateEntry): void {
    // Update key index
    if (!this.keyIndex.has(logicalKey)) {
      this.keyIndex.set(logicalKey, new Set());
    }
    this.keyIndex.get(logicalKey)!.add(fullKey);

    // Update TTL index
    if (entry.ttl) {
      const expiryTime = new Date(entry.timestamp).getTime() + (entry.ttl * 1000);
      this.ttlIndex.set(fullKey, expiryTime);
    }
  }

  private shouldCompress(size: number): boolean {
    return this.options.enableCompression && size > this.options.compressionThreshold;
  }

  private async compress(data: any): Promise<Buffer> {
    const jsonString = JSON.stringify(data);
    return await gzipAsync(jsonString);
  }

  private async decompress(compressedData: Buffer): Promise<any> {
    const decompressed = await gunzipAsync(compressedData);
    return JSON.parse(decompressed.toString());
  }

  private calculateChecksum(data: any): string {
    return createHash('sha256').update(JSON.stringify(data)).digest('hex');
  }

  private async saveEntry(key: string, entry: StateEntry): Promise<void> {
    this.storage.set(key, entry);
  }

  private async saveInTransaction(txId: string, key: string, entry: StateEntry): Promise<void> {
    const context = this.activeTransactions.get(txId);
    if (!context) {
      throw new Error(`Transaction not found: ${txId}`);
    }

    // Store rollback data (only if not already stored for this key)
    if (!context.rollbackData.has(key)) {
      const existingEntry = this.storage.get(key);
      context.rollbackData.set(key, existingEntry);
    }

    // Record operation
    context.operations.push({
      type: 'save',
      key,
      data: entry,
      previousData: this.storage.get(key)
    });

    // Apply operation immediately (will be rolled back if needed)
    this.storage.set(key, entry);
    
    // Update indices temporarily (will be rolled back if needed)
    this.updateIndices(entry.logicalKey, key, entry);
  }

  private async loadFromPersistence(): Promise<void> {
    try {
      const data = await fs.readFile(this.databaseFile, 'utf-8');
      const state = JSON.parse(data);
      
      if (state.version === '1.0.0') {
        await this.importState(state);
        console.log(`📁 Loaded ${state.entries.length} entries from persistence`);
      }
    } catch (error) {
      // File doesn't exist or is corrupted, start fresh
      console.log('📁 Starting with fresh state (no existing persistence file)');
    }
  }

  private async persistToDisk(): Promise<void> {
    try {
      const exportedState = await this.exportState();
      await fs.writeFile(this.databaseFile, JSON.stringify(exportedState, null, 2));
    } catch (error) {
      console.error('Failed to persist state to disk:', error);
      throw error;
    }
  }

  /**
   * Cleanup and shutdown
   */
  async shutdown(): Promise<void> {
    this.stopGarbageCollection();
    await this.persistToDisk();
    
    // Rollback any active transactions
    for (const txId of this.activeTransactions.keys()) {
      await this.rollbackTransaction(txId);
    }
    
    this.emit('stateManagerShutdown');
  }
}