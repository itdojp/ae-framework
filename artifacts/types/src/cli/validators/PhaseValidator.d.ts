import { AEFrameworkConfig, Phase, ValidationResult, Prerequisite } from '../types.js';
export declare class PhaseValidator {
    private config;
    constructor(config: AEFrameworkConfig);
    validate(phase: Phase): Promise<ValidationResult>;
    validatePrerequisite(prereq: Prerequisite): Promise<ValidationResult>;
    hasRequiredArtifacts(phase: Phase): Promise<boolean>;
    private checkArtifactExists;
    private runValidation;
    private validateTestsExist;
    private validateTestsAreRed;
    private validateTestsPass;
    private validateCodeHasTests;
    private validateCoverage;
    private runFullTestSuite;
    private validateTraceability;
}
