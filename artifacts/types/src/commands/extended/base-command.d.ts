/**
 * Base Command for Extended Commands
 * Provides common functionality and unified interface
 */
import type { CommandResult, CommandContext } from '../slash-command-manager.js';
import { EvidenceValidator } from '../../utils/evidence-validator.js';
export interface ExtendedCommandConfig {
    name: string;
    description: string;
    usage: string;
    aliases?: string[];
    category: 'utility' | 'analysis' | 'documentation';
}
export interface ExtendedCommandResult<T = any> {
    success: boolean;
    message: string;
    data?: T;
    evidence?: any[];
    metrics?: CommandMetrics;
}
export interface CommandMetrics {
    executionTime: number;
    filesProcessed: number;
    confidence?: number;
}
export declare abstract class BaseExtendedCommand {
    readonly name: string;
    readonly description: string;
    readonly category: "utility";
    readonly usage: string;
    readonly aliases?: string[];
    protected validator: EvidenceValidator;
    private metrics;
    constructor(config?: ExtendedCommandConfig);
    /**
     * Record metric for performance tracking
     */
    protected recordMetric(key: string, value?: number): void;
    /**
     * Get recorded metrics
     */
    protected getMetrics(): Map<string, number>;
    /**
     * Main handler method - implements common flow
     */
    handler(args: string[], context: CommandContext): Promise<CommandResult>;
    /**
     * Validate command arguments
     */
    protected abstract validateArgs(args: string[]): {
        isValid: boolean;
        message?: string;
    };
    /**
     * Parse command options
     */
    protected parseOptions(args: string[]): Record<string, any>;
    /**
     * Execute the specific command logic
     */
    protected abstract execute(args: string[], options: Record<string, any>, context: CommandContext): Promise<ExtendedCommandResult>;
    /**
     * Validate results with evidence
     */
    protected validateWithEvidence(data: any, options: Record<string, any>): Promise<any[]>;
    /**
     * Generate validation claim from data
     */
    protected abstract generateValidationClaim(data: any): string;
    /**
     * Generate summary for results
     */
    protected abstract generateSummary(data: any): string;
}
