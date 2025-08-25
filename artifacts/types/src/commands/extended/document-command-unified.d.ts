/**
 * Unified Document Command for ae-framework
 * Generates comprehensive documentation with unified interface
 */
import { BaseExtendedCommand, ExtendedCommandResult } from './base-command.js';
import type { CommandContext } from '../slash-command-manager.js';
import { DocumentationResult, DocumentationOptions } from './types.js';
export declare class UnifiedDocumentCommand extends BaseExtendedCommand {
    constructor();
    protected validateArgs(args: string[]): {
        isValid: boolean;
        message?: string;
    };
    protected parseOptions(args: string[]): DocumentationOptions;
    protected execute(args: string[], options: DocumentationOptions, context: CommandContext): Promise<ExtendedCommandResult<DocumentationResult>>;
    private generateDocumentation;
    private findSourceFiles;
    private documentFile;
    private parseTypeScriptFile;
    private parseJavaScriptFile;
    private hasPrivateModifier;
    private createFunctionItem;
    private createClassItem;
    private createInterfaceItem;
    private createTypeItem;
    private createConstantItem;
    private createEnumItem;
    private getFunctionSignature;
    private extractParameters;
    private extractReturnType;
    private getTypeString;
    private extractJSDocComment;
    private extractParameterComment;
    private extractReturnComment;
    private extractJSDocFromLines;
    private extractExamples;
    private extractDependencies;
    private calculateDocumentationCoverage;
    private generateDocumentationSuggestions;
    private formatDocumentation;
    private formatAsMarkdown;
    private formatAsJSDoc;
    private getOutputPath;
    private calculateDocumentationCompleteness;
    private createDocumentationSummary;
    protected generateValidationClaim(data: DocumentationResult): string;
    protected generateSummary(data: DocumentationResult): string;
}
