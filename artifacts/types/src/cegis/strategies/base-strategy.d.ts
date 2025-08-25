/**
 * Base Fix Strategy Interface
 * Phase 2.1: Abstract base class for all fix strategies
 */
import { FailureArtifact, FixStrategy, RepairAction, FailureCategory } from '../types.js';
export declare abstract class BaseFixStrategy implements FixStrategy {
    abstract readonly name: string;
    abstract readonly category: FailureCategory;
    abstract readonly confidence: number;
    abstract readonly riskLevel: number;
    abstract readonly description: string;
    /**
     * Check if this strategy can be applied to the given failure
     */
    abstract canApply(failure: FailureArtifact): Promise<boolean>;
    /**
     * Generate repair actions for the given failure
     */
    abstract generateFix(failure: FailureArtifact): Promise<RepairAction[]>;
    /**
     * Common validation for repair actions
     */
    protected validateRepairAction(action: RepairAction): boolean;
    /**
     * Helper method to create a code change repair action
     */
    protected createCodeChangeAction(description: string, filePath: string, oldCode: string, newCode: string, startLine: number, endLine: number, confidence?: number, riskLevel?: number): RepairAction;
    /**
     * Helper method to create a dependency update action
     */
    protected createDependencyUpdateAction(description: string, packageName: string, fromVersion: string, toVersion: string, confidence?: number, riskLevel?: number): RepairAction;
    /**
     * Helper method to create a type annotation action
     */
    protected createTypeAnnotationAction(description: string, filePath: string, oldCode: string, newCode: string, startLine: number, endLine: number, confidence?: number): RepairAction;
    /**
     * Helper method to create a test update action
     */
    protected createTestUpdateAction(description: string, filePath: string, oldCode: string, newCode: string, startLine: number, endLine: number, confidence?: number): RepairAction;
    /**
     * Helper method to create a validation update action
     */
    protected createValidationUpdateAction(description: string, filePath: string, oldSchema: string, newSchema: string, confidence?: number): RepairAction;
    /**
     * Helper method to extract code context around a location
     */
    protected extractCodeContext(filePath: string, startLine: number, endLine: number, contextLines?: number): Promise<string>;
    /**
     * Helper method to check if a file exists
     */
    protected fileExists(filePath: string): Promise<boolean>;
    /**
     * Helper method to parse TypeScript error message
     */
    protected parseTypeScriptError(message: string): {
        code: string;
        type: string;
        description: string;
    } | null;
    /**
     * Get TypeScript error type based on error code
     */
    private getTypeScriptErrorType;
    /**
     * Helper method to determine confidence based on error patterns
     */
    protected calculateConfidence(failure: FailureArtifact): number;
    /**
     * Helper method to assess risk level
     */
    protected assessRiskLevel(failure: FailureArtifact, changeType: 'code' | 'dependency' | 'config'): number;
}
