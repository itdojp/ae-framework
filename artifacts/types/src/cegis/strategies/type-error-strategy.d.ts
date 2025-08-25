/**
 * TypeScript Type Error Fix Strategy
 * Phase 2.1: Automatic fixes for common TypeScript compilation errors
 */
import { BaseFixStrategy } from './base-strategy.js';
import { FailureArtifact, RepairAction, FailureCategory } from '../types.js';
export declare class TypeErrorFixStrategy extends BaseFixStrategy {
    readonly name = "TypeScript Type Error Fix";
    readonly category: FailureCategory;
    readonly confidence = 0.8;
    readonly riskLevel = 1;
    readonly description = "Automatically fixes common TypeScript type errors including missing imports, type annotations, and interface mismatches";
    canApply(failure: FailureArtifact): Promise<boolean>;
    generateFix(failure: FailureArtifact): Promise<RepairAction[]>;
    private fixNameNotFound;
    private fixPropertyNotFound;
    private fixModuleNotFound;
    private fixTypeAssignmentError;
    private fixArgumentTypeMismatch;
    private fixMissingProperties;
    private fixGenericTypeError;
    private getCommonImports;
    private inferTypeAnnotation;
}
