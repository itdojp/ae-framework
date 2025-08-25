/**
 * Contract Violation Fix Strategy
 * Phase 2.1: Automatic fixes for runtime conformance violations
 */
import { BaseFixStrategy } from './base-strategy.js';
import { FailureArtifact, RepairAction, FailureCategory } from '../types.js';
export declare class ContractViolationFixStrategy extends BaseFixStrategy {
    readonly name = "Contract Violation Fix";
    readonly category: FailureCategory;
    readonly confidence = 0.8;
    readonly riskLevel = 2;
    readonly description = "Automatically fixes runtime contract violations by updating validation schemas and adding proper data transformations";
    canApply(failure: FailureArtifact): Promise<boolean>;
    generateFix(failure: FailureArtifact): Promise<RepairAction[]>;
    private fixInputViolation;
    private fixOutputViolation;
    private fixSchemaViolation;
    private extractActualData;
    private generateZodSchema;
    private inferZodType;
    private generateDataTransformation;
    private generateOutputTransformation;
    private identifyOptionalFields;
    private generateOptionalFieldsSchema;
    private generateSchemaUpdate;
    private generateVersionedSchema;
}
