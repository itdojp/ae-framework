/**
 * Failure Artifact Factory
 * Phase 2.1: Factory for creating standardized failure artifacts
 */
import { FailureArtifact, CodeLocation } from './types.js';
export declare class FailureArtifactFactory {
    /**
     * Create failure artifact from a runtime error
     */
    static fromError(error: Error, location?: CodeLocation, context?: Record<string, any>): FailureArtifact;
    /**
     * Create failure artifact from test failure
     */
    static fromTestFailure(testName: string, expected: any, actual: any, location?: CodeLocation, testOutput?: string): FailureArtifact;
    /**
     * Create failure artifact from TypeScript compilation error
     */
    static fromTypeError(message: string, filePath: string, line: number, column: number, sourceCode?: string): FailureArtifact;
    /**
     * Create failure artifact from contract violation
     */
    static fromContractViolation(contractName: string, violationType: 'input' | 'output' | 'schema', actualData: any, location?: CodeLocation, expectedSchema?: string): FailureArtifact;
    /**
     * Create failure artifact from build error
     */
    static fromBuildError(message: string, command: string, exitCode: number, buildOutput: string, workingDirectory?: string): FailureArtifact;
    /**
     * Create failure artifact from lint error
     */
    static fromLintError(rule: string, message: string, filePath: string, line: number, column: number, severity?: 'error' | 'warning', sourceCode?: string): FailureArtifact;
    /**
     * Create failure artifact from dependency issue
     */
    static fromDependencyIssue(packageName: string, issueType: 'missing' | 'version_mismatch' | 'security_vulnerability' | 'deprecated', message: string, currentVersion?: string, requiredVersion?: string): FailureArtifact;
    /**
     * Create failure artifact from performance issue
     */
    static fromPerformanceIssue(metric: string, threshold: number, actual: number, location?: CodeLocation, context?: Record<string, any>): FailureArtifact;
    /**
     * Validate and enrich an existing failure artifact
     */
    static validate(artifact: any): FailureArtifact;
    /**
     * Create a collection of related failure artifacts
     */
    static createRelatedGroup(artifacts: Partial<FailureArtifact>[], groupId?: string): FailureArtifact[];
}
