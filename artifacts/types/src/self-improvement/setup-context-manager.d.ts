/**
 * Phase 1: ContextManager Setup for Efficient Development
 *
 * This module configures the ContextManager with optimal settings for
 * the self-improvement development process, enabling efficient context
 * management during TypeScript error fixes and codebase improvements.
 */
import { ContextManager, ContextOptions } from '../utils/context-manager.js';
export interface ContextSetupResult {
    success: boolean;
    contextManager: ContextManager;
    initialContext: any;
    optimizedSettings: ContextOptions;
    errors: string[];
    recommendations: string[];
}
export declare class ContextManagerSetup {
    private contextManager;
    private phaseStateManager;
    private projectRoot;
    constructor(projectRoot?: string);
    /**
     * Set up ContextManager with optimal settings for Phase 1 development
     */
    setupForPhase1(): Promise<ContextSetupResult>;
    /**
     * Initialize Phase 1 in the phase state manager
     */
    private initializePhase1;
    /**
     * Set up working memory with TypeScript-specific patterns and solutions
     */
    private setupTypeScriptWorkingMemory;
    /**
     * Add items to working memory through context manager
     */
    private addToWorkingMemory;
    /**
     * Validate the context manager setup
     */
    private validateSetup;
    /**
     * Generate a setup report
     */
    generateSetupReport(result: ContextSetupResult): string;
}
export default ContextManagerSetup;
