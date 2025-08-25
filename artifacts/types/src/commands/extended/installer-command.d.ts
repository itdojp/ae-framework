/**
 * Installer Command for ae-framework
 * Provides project template installation and setup functionality
 */
import { BaseExtendedCommand, ExtendedCommandResult, ExtendedCommandConfig } from './base-command.js';
import { InstallationTemplate } from '../../utils/installer-manager.js';
export interface InstallerCommandResult extends ExtendedCommandResult {
    installedTemplate?: string;
    installedDependencies?: string[];
    createdFiles?: string[];
    suggestions?: string[];
    recommendations?: string[];
    availableTemplates?: InstallationTemplate[];
}
export declare class InstallerCommand extends BaseExtendedCommand {
    readonly name = "/ae:installer";
    readonly description = "Install project templates and manage dependencies";
    readonly category: "utility";
    readonly usage = "/ae:installer <template-id> | list | suggest | templates";
    readonly aliases: string[];
    private installerManager?;
    private contextManager?;
    private tokenOptimizer?;
    constructor(config?: ExtendedCommandConfig);
    private getInstallerManager;
    private getContextManager;
    private getTokenOptimizer;
    handler(args: string[], context: any): Promise<InstallerCommandResult>;
    private handleListTemplates;
    private handleSuggestTemplates;
    private handleInstallTemplate;
    private parseInstallationOptions;
    private generatePostInstallationRecommendations;
    private handleHelp;
    private createErrorResult;
    protected validateArgs(args: string[]): {
        isValid: boolean;
        message?: string;
    };
    protected execute(args: string[], options: Record<string, any>, context: any): Promise<ExtendedCommandResult>;
    protected generateValidationClaim(data: any): string;
    protected generateSummary(data: any): string;
}
