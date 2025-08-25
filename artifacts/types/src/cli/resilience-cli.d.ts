#!/usr/bin/env node
import { Command } from 'commander';
/**
 * Resilience System CLI
 * Provides command-line interface for resilience pattern management and monitoring
 */
export declare class ResilienceCLI {
    private systems;
    constructor();
    /**
     * Create a resilience system with configuration
     */
    createSystem(options: {
        name: string;
        preset?: 'default' | 'aggressive' | 'conservative' | 'minimal';
        config?: string;
    }): Promise<void>;
    /**
     * List all resilience systems
     */
    listSystems(): Promise<void>;
    /**
     * Get detailed health statistics
     */
    getHealth(systemName?: string): Promise<void>;
    /**
     * Reset resilience system statistics
     */
    resetSystem(systemName?: string): Promise<void>;
    /**
     * Test resilience system with simulated operations
     */
    testSystem(options: {
        systemName?: string;
        operations?: number;
        failureRate?: number;
        bulkheadName?: string;
    }): Promise<void>;
    /**
     * Export system configuration
     */
    exportConfig(systemName?: string, outputPath?: string): Promise<void>;
}
/**
 * Create resilience command for CLI
 */
export declare function createResilienceCommand(): Command;
