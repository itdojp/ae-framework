/**
 * Conformance CLI Interface
 * Phase 2.2: Command-line interface for runtime conformance verification
 */
import { Command } from 'commander';
export declare class ConformanceCli {
    private engine;
    private config;
    constructor();
    /**
     * Create and configure the CLI command
     */
    createCommand(): Command;
    /**
     * Handle the verify command
     */
    private handleVerifyCommand;
    /**
     * Handle the rules command
     */
    private handleRulesCommand;
    /**
     * Handle the config command
     */
    private handleConfigCommand;
    /**
     * Handle the metrics command
     */
    private handleMetricsCommand;
    /**
     * Handle the status command
     */
    private handleStatusCommand;
    /**
     * Handle the sample command
     */
    private handleSampleCommand;
    /**
     * Display verification results
     */
    private displayVerificationResults;
    /**
     * Create default runtime context
     */
    private createDefaultContext;
    /**
     * Load default configuration
     */
    private loadDefaultConfig;
    /**
     * Parse configuration value
     */
    private parseConfigValue;
    /**
     * Create sample rules for demonstration
     */
    private createSampleRules;
    /**
     * Create sample data for testing
     */
    private createSampleData;
    /**
     * Simple UUID generator
     */
    private generateUUID;
}
/**
 * Execute the Conformance CLI
 */
export declare function executeConformanceCli(args: string[]): Promise<void>;
