/**
 * Unified Troubleshoot Command for ae-framework
 * Provides intelligent debugging and problem diagnosis with unified interface
 */
import { BaseExtendedCommand, ExtendedCommandResult } from './base-command.js';
import type { CommandContext } from '../slash-command-manager.js';
import { TroubleshootResult, TroubleshootOptions } from './types.js';
export declare class UnifiedTroubleshootCommand extends BaseExtendedCommand {
    constructor();
    protected validateArgs(args: string[]): {
        isValid: boolean;
        message?: string;
    };
    protected parseOptions(args: string[]): TroubleshootOptions;
    protected execute(args: string[], options: TroubleshootOptions, context: CommandContext): Promise<ExtendedCommandResult<TroubleshootResult>>;
    private extractDescription;
    private performTroubleshooting;
    private autoDetectIssues;
    private checkPackageJson;
    private checkBuildStatus;
    private checkCommonFileIssues;
    private checkTypeScriptConfig;
    private analyzeErrorMessage;
    private analyzeLogs;
    private analyzeDescription;
    private getCategorySolutions;
    private calculateComplexityScore;
    private calculateOverallConfidence;
    private createTroubleshootSummary;
    protected generateValidationClaim(data: TroubleshootResult): string;
    protected generateSummary(data: TroubleshootResult): string;
}
