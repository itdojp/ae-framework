/**
 * Unified Analyze Command for ae-framework
 * Provides deep code analysis with unified interface
 */
import { BaseExtendedCommand, ExtendedCommandResult } from './base-command.js';
import type { CommandContext } from '../slash-command-manager.js';
import { CodeAnalysis, AnalysisOptions } from './types.js';
export declare class UnifiedAnalyzeCommand extends BaseExtendedCommand {
    constructor();
    protected validateArgs(args: string[]): {
        isValid: boolean;
        message?: string;
    };
    protected parseOptions(args: string[]): AnalysisOptions;
    protected execute(args: string[], options: AnalysisOptions, context: CommandContext): Promise<ExtendedCommandResult<CodeAnalysis>>;
    private performAnalysis;
    private analyzeFile;
    private performBasicAnalysis;
    private performSecurityAnalysis;
    private performPerformanceAnalysis;
    private performTypeScriptAnalysis;
    private calculateCodeMetrics;
    private extractDependencies;
    private calculateCyclomaticComplexity;
    private calculateCognitiveComplexity;
    private calculateFileCognitiveComplexity;
    private findSourceFiles;
    private calculateOverallConfidence;
    private createSummary;
    protected generateValidationClaim(data: CodeAnalysis): string;
    protected generateSummary(data: CodeAnalysis): string;
}
