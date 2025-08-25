/**
 * Test Failure Fix Strategy
 * Phase 2.1: Automatic fixes for common test failures and assertion errors
 */
import { BaseFixStrategy } from './base-strategy.js';
import { FailureArtifact, RepairAction, FailureCategory } from '../types.js';
export declare class TestFailureFixStrategy extends BaseFixStrategy {
    readonly name = "Test Failure Fix";
    readonly category: FailureCategory;
    readonly confidence = 0.7;
    readonly riskLevel = 1;
    readonly description = "Automatically fixes common test failures including assertion mismatches, mock issues, and async test problems";
    canApply(failure: FailureArtifact): Promise<boolean>;
    generateFix(failure: FailureArtifact): Promise<RepairAction[]>;
    private isAssertionError;
    private isAsyncTestError;
    private isMockError;
    private isTimeoutError;
    private isMatcherError;
    private fixAssertionError;
    private fixAsyncTestError;
    private fixMockError;
    private fixTimeoutError;
    private fixMatcherError;
    private isNumberComparisonError;
    private isStringComparisonError;
    private isArrayComparisonError;
    private isObjectComparisonError;
    private fixNumberComparison;
    private fixStringComparison;
    private fixArrayComparison;
    private fixObjectComparison;
    private updateAssertion;
}
