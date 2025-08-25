/**
 * CEGIS CLI Interface
 * Phase 2.1: Command-line interface for automatic code fixing
 */
import { Command } from 'commander';
export declare class CEGISCli {
    private engine;
    constructor();
    /**
     * Create and configure the CLI command
     */
    createCommand(): Command;
    /**
     * Handle the apply command
     */
    private handleApplyCommand;
    /**
     * Handle the analyze command
     */
    private handleAnalyzeCommand;
    /**
     * Handle the create-artifact command
     */
    private handleCreateArtifactCommand;
    /**
     * Handle the status command
     */
    private handleStatusCommand;
    /**
     * Handle the strategies command
     */
    private handleStrategiesCommand;
    /**
     * Load failure artifacts from file
     */
    private loadFailures;
    /**
     * Display fix results
     */
    private displayResults;
    /**
     * Group failures by category
     */
    private groupByCategory;
}
/**
 * Execute the CEGIS CLI
 */
export declare function executeCEGISCli(args: string[]): Promise<void>;
