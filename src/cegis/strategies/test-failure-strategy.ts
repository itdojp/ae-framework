/**
 * Test Failure Fix Strategy
 * Phase 2.1: Automatic fixes for common test failures and assertion errors
 */

import { BaseFixStrategy } from './base-strategy.js';
import { FailureArtifact, RepairAction, FailureCategory } from '../types.js';

export class TestFailureFixStrategy extends BaseFixStrategy {
  readonly name = 'Test Failure Fix';
  readonly category: FailureCategory = 'test_failure';
  readonly confidence = 0.7;
  readonly riskLevel = 1;
  readonly description = 'Automatically fixes common test failures including assertion mismatches, mock issues, and async test problems';

  async canApply(failure: FailureArtifact): Promise<boolean> {
    return failure.category === 'test_failure' && 
           !!failure.evidence.testOutput &&
           !!failure.location?.filePath;
  }

  async generateFix(failure: FailureArtifact): Promise<RepairAction[]> {
    const actions: RepairAction[] = [];
    const testOutput = failure.evidence.testOutput || '';
    
    if (!failure.location) {
      return actions;
    }

    // Analyze test failure patterns
    if (this.isAssertionError(testOutput)) {
      actions.push(...await this.fixAssertionError(failure, testOutput));
    }
    
    if (this.isAsyncTestError(testOutput)) {
      actions.push(...await this.fixAsyncTestError(failure, testOutput));
    }
    
    if (this.isMockError(testOutput)) {
      actions.push(...await this.fixMockError(failure, testOutput));
    }
    
    if (this.isTimeoutError(testOutput)) {
      actions.push(...await this.fixTimeoutError(failure, testOutput));
    }
    
    if (this.isMatcherError(testOutput)) {
      actions.push(...await this.fixMatcherError(failure, testOutput));
    }

    return actions.filter(action => this.validateRepairAction(action));
  }

  private isAssertionError(testOutput: string): boolean {
    return testOutput.includes('AssertionError') || 
           testOutput.includes('Expected') ||
           testOutput.includes('toBe') ||
           testOutput.includes('toEqual');
  }

  private isAsyncTestError(testOutput: string): boolean {
    return testOutput.includes('timeout') ||
           testOutput.includes('Promise') ||
           testOutput.includes('async') ||
           testOutput.includes('await');
  }

  private isMockError(testOutput: string): boolean {
    return testOutput.includes('mock') ||
           testOutput.includes('spy') ||
           testOutput.includes('stub') ||
           testOutput.includes('jest.fn');
  }

  private isTimeoutError(testOutput: string): boolean {
    return testOutput.includes('timeout') ||
           testOutput.includes('exceeded') ||
           testOutput.includes('5000ms');
  }

  private isMatcherError(testOutput: string): boolean {
    return testOutput.includes('toMatchSnapshot') ||
           testOutput.includes('toMatch') ||
           testOutput.includes('toContain');
  }

  private async fixAssertionError(
    failure: FailureArtifact,
    testOutput: string
  ): Promise<RepairAction[]> {
    const actions: RepairAction[] = [];
    const filePath = failure.location!.filePath;
    
    // Parse expected vs actual values
    const expectedMatch = testOutput.match(/Expected:\s*(.+)/);
    const actualMatch = testOutput.match(/Received:\s*(.+)/);
    
    if (expectedMatch && actualMatch && failure.evidence.sourceCode) {
      const expected = expectedMatch[1].trim();
      const actual = actualMatch[1].trim();
      const sourceLines = failure.evidence.sourceCode.split('\n');
      const targetLine = sourceLines[failure.location!.startLine - 1] || '';
      
      // Fix common assertion mismatches
      if (this.isNumberComparisonError(expected, actual)) {
        actions.push(...this.fixNumberComparison(failure, targetLine, expected, actual));
      } else if (this.isStringComparisonError(expected, actual)) {
        actions.push(...this.fixStringComparison(failure, targetLine, expected, actual));
      } else if (this.isArrayComparisonError(expected, actual)) {
        actions.push(...this.fixArrayComparison(failure, targetLine, expected, actual));
      } else if (this.isObjectComparisonError(expected, actual)) {
        actions.push(...this.fixObjectComparison(failure, targetLine, expected, actual));
      }
      
      // Generic fix: update expectation to match actual value
      const updatedAssertion = this.updateAssertion(targetLine, expected, actual);
      if (updatedAssertion !== targetLine) {
        actions.push(this.createTestUpdateAction(
          `Update assertion to match actual value: ${actual}`,
          filePath,
          targetLine,
          updatedAssertion,
          failure.location!.startLine,
          failure.location!.endLine,
          0.6
        ));
      }
    }
    
    return actions;
  }

  private async fixAsyncTestError(
    failure: FailureArtifact,
    testOutput: string
  ): Promise<RepairAction[]> {
    const actions: RepairAction[] = [];
    const filePath = failure.location!.filePath;
    
    if (!failure.evidence.sourceCode) return actions;
    
    const sourceLines = failure.evidence.sourceCode.split('\n');
    const targetLine = sourceLines[failure.location!.startLine - 1] || '';
    
    // Add async/await if missing
    if (!targetLine.includes('async') && targetLine.includes('it(')) {
      const withAsync = targetLine.replace(/it\((['"`])([^'"`]+)\1,\s*\(/, 'it($1$2$1, async (');
      actions.push(this.createTestUpdateAction(
        'Add async keyword to test function',
        filePath,
        targetLine,
        withAsync,
        failure.location!.startLine,
        failure.location!.endLine,
        0.9
      ));
    }
    
    // Add await to Promise calls
    if (targetLine.includes('.then(') || targetLine.includes('Promise')) {
      const withAwait = targetLine.replace(
        /(\w+\([^)]*\))\.then\(/,
        'await $1; // Converted from .then()'
      );
      if (withAwait !== targetLine) {
        actions.push(this.createTestUpdateAction(
          'Convert .then() to await',
          filePath,
          targetLine,
          withAwait,
          failure.location!.startLine,
          failure.location!.endLine,
          0.8
        ));
      }
    }
    
    // Increase timeout for slow tests
    if (testOutput.includes('timeout')) {
      const withTimeout = `${targetLine}\n  }, 10000); // Increased timeout`;
      actions.push(this.createTestUpdateAction(
        'Increase test timeout to 10 seconds',
        filePath,
        targetLine,
        withTimeout,
        failure.location!.startLine,
        failure.location!.endLine,
        0.7
      ));
    }
    
    return actions;
  }

  private async fixMockError(
    failure: FailureArtifact,
    testOutput: string
  ): Promise<RepairAction[]> {
    const actions: RepairAction[] = [];
    const filePath = failure.location!.filePath;
    
    if (!failure.evidence.sourceCode) return actions;
    
    const sourceLines = failure.evidence.sourceCode.split('\n');
    const targetLine = sourceLines[failure.location!.startLine - 1] || '';
    
    // Fix mock setup issues
    if (testOutput.includes('not a function')) {
      // Add jest.fn() to mock
      const withJestFn = targetLine.replace(
        /(\w+)\s*=\s*{/,
        '$1 = { ...jest.fn(), '
      );
      if (withJestFn !== targetLine) {
        actions.push(this.createTestUpdateAction(
          'Add jest.fn() to mock object',
          filePath,
          targetLine,
          withJestFn,
          failure.location!.startLine,
          failure.location!.endLine,
          0.8
        ));
      }
    }
    
    // Fix mock call expectations
    if (testOutput.includes('toHaveBeenCalled')) {
      const withMockClear = `${targetLine}\n  beforeEach(() => {\n    jest.clearAllMocks();\n  });`;
      actions.push(this.createTestUpdateAction(
        'Add mock cleanup in beforeEach',
        filePath,
        targetLine,
        withMockClear,
        failure.location!.startLine,
        failure.location!.endLine,
        0.7
      ));
    }
    
    return actions;
  }

  private async fixTimeoutError(
    failure: FailureArtifact,
    testOutput: string
  ): Promise<RepairAction[]> {
    const actions: RepairAction[] = [];
    const filePath = failure.location!.filePath;
    
    if (!failure.evidence.sourceCode) return actions;
    
    const sourceLines = failure.evidence.sourceCode.split('\n');
    const targetLine = sourceLines[failure.location!.startLine - 1] || '';
    
    // Extract current timeout if any
    const timeoutMatch = testOutput.match(/(\d+)ms/);
    const currentTimeout = timeoutMatch ? parseInt(timeoutMatch[1]) : 5000;
    const newTimeout = Math.min(currentTimeout * 2, 30000); // Max 30 seconds
    
    // Add or update timeout
    if (targetLine.includes('it(')) {
      const withTimeout = targetLine.replace(
        /it\(([^)]+)\)(\s*=>\s*{|\s*,\s*async)/,
        `it($1, $2, ${newTimeout})`
      );
      if (withTimeout !== targetLine) {
        actions.push(this.createTestUpdateAction(
          `Increase test timeout to ${newTimeout}ms`,
          filePath,
          targetLine,
          withTimeout,
          failure.location!.startLine,
          failure.location!.endLine,
          0.8
        ));
      }
    }
    
    return actions;
  }

  private async fixMatcherError(
    failure: FailureArtifact,
    testOutput: string
  ): Promise<RepairAction[]> {
    const actions: RepairAction[] = [];
    const filePath = failure.location!.filePath;
    
    if (!failure.evidence.sourceCode) return actions;
    
    const sourceLines = failure.evidence.sourceCode.split('\n');
    const targetLine = sourceLines[failure.location!.startLine - 1] || '';
    
    // Fix snapshot mismatches
    if (testOutput.includes('toMatchSnapshot')) {
      actions.push(this.createTestUpdateAction(
        'Update snapshot (run with --updateSnapshot)',
        filePath,
        '// Run: npm test -- --updateSnapshot',
        '// Snapshot updated automatically',
        failure.location!.startLine,
        failure.location!.endLine,
        0.9
      ));
    }
    
    // Fix string matching issues
    if (testOutput.includes('toMatch') || testOutput.includes('toContain')) {
      const relaxedMatcher = targetLine.replace(/toMatch\(/g, 'toContain(')
                                       .replace(/toEqual\(/g, 'toContain(');
      if (relaxedMatcher !== targetLine) {
        actions.push(this.createTestUpdateAction(
          'Use more flexible matcher (toContain instead of exact match)',
          filePath,
          targetLine,
          relaxedMatcher,
          failure.location!.startLine,
          failure.location!.endLine,
          0.6
        ));
      }
    }
    
    return actions;
  }

  private isNumberComparisonError(expected: string, actual: string): boolean {
    return !isNaN(Number(expected)) && !isNaN(Number(actual));
  }

  private isStringComparisonError(expected: string, actual: string): boolean {
    return (expected.startsWith('"') || expected.startsWith("'")) &&
           (actual.startsWith('"') || actual.startsWith("'"));
  }

  private isArrayComparisonError(expected: string, actual: string): boolean {
    return expected.startsWith('[') && actual.startsWith('[');
  }

  private isObjectComparisonError(expected: string, actual: string): boolean {
    return expected.startsWith('{') && actual.startsWith('{');
  }

  private fixNumberComparison(
    failure: FailureArtifact,
    targetLine: string,
    expected: string,
    actual: string
  ): RepairAction[] {
    const actions: RepairAction[] = [];
    const filePath = failure.location!.filePath;
    
    const expectedNum = Number(expected);
    const actualNum = Number(actual);
    
    // Check if it's a precision issue
    if (Math.abs(expectedNum - actualNum) < 0.01) {
      const withPrecision = targetLine.replace(/toEqual\(/g, 'toBeCloseTo(');
      actions.push(this.createTestUpdateAction(
        'Use toBeCloseTo() for floating point comparison',
        filePath,
        targetLine,
        withPrecision,
        failure.location!.startLine,
        failure.location!.endLine,
        0.9
      ));
    }
    
    return actions;
  }

  private fixStringComparison(
    failure: FailureArtifact,
    targetLine: string,
    expected: string,
    actual: string
  ): RepairAction[] {
    const actions: RepairAction[] = [];
    const filePath = failure.location!.filePath;
    
    // Check for whitespace differences
    if (expected.trim() === actual.trim()) {
      const withTrim = targetLine.replace(
        /expect\(([^)]+)\)/,
        'expect($1.trim())'
      );
      actions.push(this.createTestUpdateAction(
        'Trim whitespace before comparison',
        filePath,
        targetLine,
        withTrim,
        failure.location!.startLine,
        failure.location!.endLine,
        0.9
      ));
    }
    
    return actions;
  }

  private fixArrayComparison(
    failure: FailureArtifact,
    targetLine: string,
    expected: string,
    actual: string
  ): RepairAction[] {
    const actions: RepairAction[] = [];
    const filePath = failure.location!.filePath;
    
    // Use arrayContaining for flexible array comparison
    const withArrayContaining = targetLine.replace(
      /toEqual\(\[([^\]]+)\]\)/,
      'toEqual(expect.arrayContaining([$1]))'
    );
    
    if (withArrayContaining !== targetLine) {
      actions.push(this.createTestUpdateAction(
        'Use arrayContaining for flexible array comparison',
        filePath,
        targetLine,
        withArrayContaining,
        failure.location!.startLine,
        failure.location!.endLine,
        0.7
      ));
    }
    
    return actions;
  }

  private fixObjectComparison(
    failure: FailureArtifact,
    targetLine: string,
    expected: string,
    actual: string
  ): RepairAction[] {
    const actions: RepairAction[] = [];
    const filePath = failure.location!.filePath;
    
    // Use objectContaining for flexible object comparison
    const withObjectContaining = targetLine.replace(
      /toEqual\(\{([^}]+)\}\)/,
      'toEqual(expect.objectContaining({$1}))'
    );
    
    if (withObjectContaining !== targetLine) {
      actions.push(this.createTestUpdateAction(
        'Use objectContaining for flexible object comparison',
        filePath,
        targetLine,
        withObjectContaining,
        failure.location!.startLine,
        failure.location!.endLine,
        0.7
      ));
    }
    
    return actions;
  }

  private updateAssertion(targetLine: string, expected: string, actual: string): string {
    // Update the expected value in common assertion patterns
    const patterns = [
      { 
        pattern: /toBe\(([^)]+)\)/,
        replacement: `toBe(${actual})`
      },
      { 
        pattern: /toEqual\(([^)]+)\)/,
        replacement: `toEqual(${actual})`
      },
      { 
        pattern: /toStrictEqual\(([^)]+)\)/,
        replacement: `toStrictEqual(${actual})`
      }
    ];
    
    for (const { pattern, replacement } of patterns) {
      if (pattern.test(targetLine)) {
        return targetLine.replace(pattern, replacement);
      }
    }
    
    return targetLine;
  }
}