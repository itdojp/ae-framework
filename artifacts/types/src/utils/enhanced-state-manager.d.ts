import { EventEmitter } from 'events';
/**
 * Minimal AEIR stub type for build fix.
 * TODO: Replace with import from '@ae-framework/spec-compiler' when available.
 */
export interface AEIR {
    id?: string;
    name?: string;
    type?: string;
    version?: string;
}
/**
 * Enhanced State Storage Entry with versioning and metadata
 */
export interface StateEntry<T = any> {
    id: string;
    logicalKey: string;
    timestamp: string;
    version: number;
    checksum: string;
    data: T;
    compressed: boolean;
    tags: Record<string, string>;
    ttl?: number;
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
    compressionThreshold?: number;
    defaultTTL?: number;
    gcInterval?: number;
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
 * Enhanced State Manager with SQLite-like storage, compression, and EventBus integration
 */
export declare class EnhancedStateManager extends EventEmitter {
    private storage;
    private keyIndex;
    private versionIndex;
    private ttlIndex;
    private activeTransactions;
    private gcTimer?;
    private isInitialized;
    private readonly options;
    private readonly dataDir;
    private readonly databaseFile;
    constructor(projectRoot?: string, options?: StorageOptions);
    /**
     * Initialize the enhanced state manager
     */
    initialize(): Promise<void>;
    /**
     * Save Single Source of Truth (SSOT) data with versioning
     */
    saveSSOT(logicalKey: string, data: AEIR, options?: {
        phase?: string;
        tags?: Record<string, string>;
        ttl?: number;
        source?: string;
        transactionId?: string;
    }): Promise<string>;
    /**
     * Load SSOT data by logical key (latest version by default)
     */
    loadSSOT(logicalKey: string, version?: number): Promise<AEIR | null>;
    /**
     * Create compressed snapshot of current state
     */
    createSnapshot(phase: string, entities?: string[]): Promise<string>;
    /**
     * Load snapshot by ID
     */
    loadSnapshot(snapshotId: string): Promise<Record<string, StateEntry> | null>;
    /**
     * Persist failure artifact and notify EventBus for CEGIS integration
     */
    persistFailureArtifact(artifact: FailureArtifact): Promise<void>;
    /**
     * Begin transaction for atomic operations
     */
    beginTransaction(): Promise<string>;
    /**
     * Commit transaction
     */
    commitTransaction(txId: string): Promise<void>;
    /**
     * Rollback transaction
     */
    rollbackTransaction(txId: string): Promise<void>;
    /**
     * Get all versions of a logical key
     */
    getVersions(logicalKey: string): Promise<Array<{
        version: number;
        timestamp: string;
        key: string;
    }>>;
    /**
     * Cleanup old versions beyond maxVersions limit
     */
    private cleanupOldVersions;
    /**
     * Start garbage collection process
     */
    private startGarbageCollection;
    /**
     * Run garbage collection to remove expired entries
     */
    private runGarbageCollection;
    /**
     * Stop garbage collection
     */
    stopGarbageCollection(): void;
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
    };
    /**
     * Export state for backup or migration
     */
    exportState(): Promise<{
        metadata: {
            version: string;
            timestamp: string;
            options: StorageOptions;
        };
        entries: StateEntry[];
        indices: {
            keyIndex: Record<string, string[]>;
            versionIndex: Record<string, number>;
        };
    }>;
    /**
     * Import state from backup or migration
     */
    importState(exportedState: Awaited<ReturnType<typeof this.exportState>>): Promise<void>;
    private ensureInitialized;
    private getNextVersion;
    private findLatestKey;
    private findKeyByVersion;
    private updateIndices;
    private shouldCompress;
    private compress;
    private decompress;
    private calculateChecksum;
    private saveEntry;
    private saveInTransaction;
    private loadFromPersistence;
    private persistToDisk;
    /**
     * Cleanup and shutdown
     */
    shutdown(): Promise<void>;
}
