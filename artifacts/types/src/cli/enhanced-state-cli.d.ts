#!/usr/bin/env node
import { Command } from 'commander';
/**
 * Enhanced State Manager CLI
 * Provides command-line interface for advanced state management operations
 */
export declare class EnhancedStateCLI {
    private stateManager;
    constructor(projectRoot?: string);
    /**
     * Initialize the state manager and CLI
     */
    initialize(): Promise<void>;
    /**
     * Save SSOT (Single Source of Truth) from file
     */
    saveSSOT(options: {
        logicalKey: string;
        inputPath: string;
        phase?: string;
        tags?: string;
        ttl?: number;
        source?: string;
    }): Promise<void>;
    /**
     * Load SSOT data
     */
    loadSSOT(options: {
        logicalKey: string;
        version?: number;
        outputPath?: string;
    }): Promise<void>;
    /**
     * List all versions of a logical key
     */
    listVersions(logicalKey: string): Promise<void>;
    /**
     * Create compressed snapshot
     */
    createSnapshot(options: {
        phase: string;
        entities?: string;
    }): Promise<void>;
    /**
     * Load and display snapshot
     */
    loadSnapshot(snapshotId: string): Promise<void>;
    /**
     * Simulate failure artifact for testing
     */
    simulateFailure(options: {
        phase: string;
        type: 'validation' | 'compilation' | 'test' | 'verification' | 'generation';
        severity: 'low' | 'medium' | 'high' | 'critical';
        message: string;
        retryable?: boolean;
    }): Promise<void>;
    /**
     * Run manual garbage collection
     */
    runGarbageCollection(): Promise<void>;
    /**
     * Display storage statistics
     */
    showStatistics(): Promise<void>;
    /**
     * Test transaction functionality
     */
    testTransaction(): Promise<void>;
    /**
     * Export state to file
     */
    exportState(outputPath: string): Promise<void>;
    /**
     * Import state from file
     */
    importState(inputPath: string): Promise<void>;
    private setupEventListeners;
    private formatBytes;
    /**
     * Cleanup and shutdown
     */
    shutdown(): Promise<void>;
}
export declare function createEnhancedStateCommand(): Command;
