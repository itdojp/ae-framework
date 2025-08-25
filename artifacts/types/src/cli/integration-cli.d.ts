/**
 * Integration Testing CLI Interface
 * Phase 2.3: Command-line interface for comprehensive integration testing
 */
import { Command } from 'commander';
export declare class IntegrationTestingCli {
    private orchestrator;
    private discovery;
    constructor();
    /**
     * Create and configure the CLI command
     */
    createCommand(): Command;
    /**
     * Handle the run command
     */
    private handleRunCommand;
    /**
     * Handle the discover command
     */
    private handleDiscoverCommand;
    /**
     * Handle the list command
     */
    private handleListCommand;
    /**
     * Handle the generate command
     */
    private handleGenerateCommand;
    /**
     * Handle the status command
     */
    private handleStatusCommand;
    /**
     * Handle the reports command
     */
    private handleReportsCommand;
    /**
     * Create default environment
     */
    private createDefaultEnvironment;
    /**
     * Display discovery results in table format
     */
    private displayDiscoveryTable;
    /**
     * Generate sample test case
     */
    private generateSampleTest;
    /**
     * Generate sample test suite
     */
    private generateSampleSuite;
    /**
     * Generate sample fixture
     */
    private generateSampleFixture;
    /**
     * Generate sample environment
     */
    private generateSampleEnvironment;
    /**
     * Format file size
     */
    private formatFileSize;
}
/**
 * Execute the Integration Testing CLI
 */
export declare function executeIntegrationCli(args: string[]): Promise<void>;
