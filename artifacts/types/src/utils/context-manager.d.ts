/**
 * Context Manager for ae-framework
 * Manages context window and optimizes information flow to AI agents
 */
import { PhaseType } from './phase-state-manager.js';
export interface ContextWindow {
    steering: string;
    phaseInfo: string;
    workingMemory: string;
    relevantFiles: string;
    totalTokens: number;
}
export interface ContextOptions {
    maxTokens?: number;
    includeHistory?: boolean;
    includeArtifacts?: boolean;
    focusPhase?: PhaseType;
    relevantKeywords?: string[];
}
export declare class ContextManager {
    private tokenOptimizer;
    private steeringLoader;
    private phaseStateManager;
    private workingMemory;
    private readonly DEFAULT_MAX_TOKENS;
    private readonly STEERING_TOKEN_BUDGET;
    private readonly PHASE_TOKEN_BUDGET;
    private readonly TOKEN_ESTIMATE_RATIO;
    private readonly FILES_TOKEN_BUDGET;
    constructor(projectRoot?: string);
    /**
     * Build optimized context for current phase
     */
    buildContext(options?: ContextOptions): Promise<ContextWindow>;
    /**
     * Build steering context with compression
     */
    private buildSteeringContext;
    /**
     * Build phase-specific context
     */
    private buildPhaseContext;
    /**
     * Build working memory context
     */
    private buildWorkingMemory;
    /**
     * Build relevant files context
     */
    private buildRelevantFiles;
    /**
     * Find relevant files based on phase and keywords
     */
    private findRelevantFiles;
    /**
     * Scan directory for files
     */
    private scanDirectory;
    /**
     * Compress file content based on type
     */
    private compressFileContent;
    /**
     * Get steering document priority based on phase
     */
    private getSteeringPriority;
    /**
     * Allocate token budget across context components
     */
    private allocateTokenBudget;
    /**
     * Add item to working memory
     */
    addToMemory(key: string, value: any): void;
    /**
     * Clear working memory
     */
    clearMemory(): void;
    /**
     * Get memory item
     */
    getFromMemory(key: string): any;
    /**
     * Estimate token count - delegates to TokenOptimizer for consistency
     */
    private estimateTokens;
    /**
     * Truncate text to token limit
     */
    private truncateToTokens;
    /**
     * Get context statistics
     */
    getContextStats(options?: ContextOptions): Promise<{
        components: Record<string, number>;
        total: number;
        compressionRatio: number;
    }>;
}
