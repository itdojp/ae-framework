/**
 * Unified Improve Command for ae-framework
 * Provides code improvements and refactoring suggestions with unified interface
 */
import { BaseExtendedCommand, ExtendedCommandResult } from './base-command.js';
import type { CommandContext } from '../slash-command-manager.js';
import { ImprovementResult, ImprovementOptions } from './types.js';
export declare class UnifiedImproveCommand extends BaseExtendedCommand {
    constructor();
    protected validateArgs(args: string[]): {
        isValid: boolean;
        message?: string;
    };
    protected parseOptions(args: string[]): ImprovementOptions;
    protected execute(args: string[], options: ImprovementOptions, context: CommandContext): Promise<ExtendedCommandResult<ImprovementResult>>;
    private analyzeForImprovements;
    private findSourceFiles;
    private analyzeFile;
    private analyzePatterns;
    private analyzeSecurityPatterns;
    private analyzePerformancePatterns;
    private analyzeModernizationPatterns;
    private analyzeTypeScriptPatterns;
    private applyImprovements;
    private calculateEstimatedImpact;
    private calculateComplexityMetric;
    private calculateOverallConfidence;
    private createImprovementSummary;
    protected generateValidationClaim(data: ImprovementResult): string;
    protected generateSummary(data: ImprovementResult): string;
}
