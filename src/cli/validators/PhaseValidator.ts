import { execSync } from 'child_process';
import { existsSync } from 'fs';
import { glob } from 'glob';
import { AEFrameworkConfig, Phase, ValidationResult, ValidationDetail, Prerequisite } from '../types.js';

export class PhaseValidator {
  constructor(private config: AEFrameworkConfig) {}

  async validate(phase: Phase): Promise<ValidationResult> {
    const details: ValidationDetail[] = [];

    // Check required artifacts
    for (const artifact of phase.required_artifacts || []) {
      const exists = await this.checkArtifactExists(artifact);
      details.push({
        check: `Required artifact: ${artifact}`,
        passed: exists,
        message: exists ? undefined : `File or directory not found: ${artifact}`
      });
    }

    // Run validation checks
    for (const validation of phase.validation || []) {
      const result = await this.runValidation(validation, phase);
      details.push({
        check: `Validation: ${validation}`,
        passed: result.passed,
        message: result.message
      });
    }

    // TDD specific validations
    if (phase.enforce_red_first) {
      const redResult = await this.validateTestsAreRed();
      details.push({
        check: 'Tests are RED (failing)',
        passed: redResult.passed,
        message: redResult.message
      });
    }

    if (phase.block_code_without_test) {
      const testCoverageResult = await this.validateCodeHasTests();
      details.push({
        check: 'All code has corresponding tests',
        passed: testCoverageResult.passed,
        message: testCoverageResult.message
      });
    }

    if (phase.mandatory_test_run) {
      const testRunResult = await this.validateTestsPass();
      details.push({
        check: 'All tests pass',
        passed: testRunResult.passed,
        message: testRunResult.message
      });
    }

    if (phase.coverage_threshold) {
      const coverageResult = await this.validateCoverage(phase.coverage_threshold);
      details.push({
        check: `Coverage >= ${phase.coverage_threshold}%`,
        passed: coverageResult.passed,
        message: coverageResult.message
      });
    }

    const success = details.every(detail => detail.passed);
    return { success, details };
  }

  async validatePrerequisite(prereq: Prerequisite): Promise<ValidationResult> {
    const phase = this.config.phases[prereq.phase];
    if (!phase) {
      return {
        success: false,
        message: `Unknown prerequisite phase: ${prereq.phase}`,
        details: []
      };
    }

    // Check if prerequisite phase artifacts exist
    const hasArtifacts = await this.hasRequiredArtifacts(phase);
    if (!hasArtifacts) {
      return {
        success: false,
        message: `Prerequisite phase ${prereq.phase} not completed`,
        details: []
      };
    }

    // Run specific prerequisite validation
    const validationResult = await this.runValidation(prereq.validation, phase);
    
    return {
      success: validationResult.passed,
      message: validationResult.message,
      details: [{
        check: prereq.validation,
        passed: validationResult.passed,
        message: validationResult.message
      }]
    };
  }

  async hasRequiredArtifacts(phase: Phase): Promise<boolean> {
    for (const artifact of phase.required_artifacts || []) {
      const exists = await this.checkArtifactExists(artifact);
      if (!exists) {
        return false;
      }
    }
    return true;
  }

  private async checkArtifactExists(pattern: string): Promise<boolean> {
    try {
      if (pattern.includes('*')) {
        const files = await glob(pattern);
        return files.length > 0;
      } else {
        return existsSync(pattern);
      }
    } catch {
      return false;
    }
  }

  private async runValidation(validation: string, phase: Phase): Promise<{ passed: boolean; message?: string }> {
    switch (validation) {
      case 'ensure_tests_exist':
        return this.validateTestsExist();
      
      case 'run_tests_expect_red':
        return this.validateTestsAreRed();
      
      case 'ensure_tests_pass':
        return this.validateTestsPass();
      
      case 'check_code_coverage':
        return this.validateCoverage(phase.coverage_threshold || 80);
      
      case 'run_full_test_suite':
        return this.runFullTestSuite();
      
      case 'verify_traceability':
        return this.validateTraceability();
      
      case 'tests_are_red':
        return this.validateTestsAreRed();
        
      default:
        return { passed: true, message: `Unknown validation: ${validation}` };
    }
  }

  private async validateTestsExist(): Promise<{ passed: boolean; message?: string }> {
    try {
      const testFiles = await glob('tests/**/*.test.ts');
      const specFiles = await glob('specs/bdd/**/*.feature');
      
      const hasTests = testFiles.length > 0 || specFiles.length > 0;
      
      return {
        passed: hasTests,
        message: hasTests ? undefined : 'No test files found'
      };
    } catch (error) {
      return { passed: false, message: `Error checking tests: ${error}` };
    }
  }

  private async validateTestsAreRed(): Promise<{ passed: boolean; message?: string }> {
    try {
      // Run tests expecting them to fail (RED phase)
      execSync('npm test --silent', { encoding: 'utf8', stdio: 'pipe' });
      
      // If tests pass when they should fail, that's a problem in RED phase
      return {
        passed: false,
        message: 'Tests are GREEN but should be RED in test-first phase'
      };
    } catch (error: any) {
      // Tests failing is expected in RED phase
      const output = error.stdout || error.stderr || '';
      const hasFailures = output.includes('failing') || output.includes('failed');
      
      return {
        passed: hasFailures,
        message: hasFailures ? 'Tests are correctly RED' : 'No test failures detected'
      };
    }
  }

  private async validateTestsPass(): Promise<{ passed: boolean; message?: string }> {
    try {
      execSync('npm test --silent', { encoding: 'utf8', stdio: 'pipe' });
      return { passed: true, message: 'All tests pass' };
    } catch (error: any) {
      const output = error.stdout || error.stderr || '';
      return {
        passed: false,
        message: `Tests failed: ${output.split('\n').slice(-5).join('\n')}`
      };
    }
  }

  private async validateCodeHasTests(): Promise<{ passed: boolean; message?: string }> {
    try {
      const srcFiles = await glob('src/**/*.ts');
      const testFiles = await glob('tests/**/*.test.ts');
      
      const srcFilesWithoutTests: string[] = [];
      
      for (const srcFile of srcFiles) {
        const baseName = srcFile.replace('src/', '').replace('.ts', '');
        const hasTest = testFiles.some(testFile => 
          testFile.includes(baseName) || testFile.includes(srcFile.split('/').pop()?.replace('.ts', '') || '')
        );
        
        if (!hasTest) {
          srcFilesWithoutTests.push(srcFile);
        }
      }
      
      const allCovered = srcFilesWithoutTests.length === 0;
      
      return {
        passed: allCovered,
        message: allCovered 
          ? 'All source files have corresponding tests'
          : `Files without tests: ${srcFilesWithoutTests.slice(0, 3).join(', ')}${srcFilesWithoutTests.length > 3 ? '...' : ''}`
      };
    } catch (error) {
      return { passed: false, message: `Error checking test coverage: ${error}` };
    }
  }

  private async validateCoverage(threshold: number): Promise<{ passed: boolean; message?: string }> {
    try {
      const result = execSync('npm run coverage --silent', { encoding: 'utf8', stdio: 'pipe' });
      
      // Parse coverage output for percentage
      const coverageMatch = result.match(/All files[^\d]*(\d+(?:\.\d+)?)/);
      const coverage = coverageMatch && coverageMatch[1] ? parseFloat(coverageMatch[1]) : 0;
      
      const passed = coverage >= threshold;
      
      return {
        passed,
        message: `Coverage: ${coverage}% (threshold: ${threshold}%)`
      };
    } catch (error) {
      return { passed: false, message: 'Could not determine coverage' };
    }
  }

  private async runFullTestSuite(): Promise<{ passed: boolean; message?: string }> {
    try {
      // Run all types of tests
      execSync('npm run test:all --silent', { encoding: 'utf8', stdio: 'pipe' });
      return { passed: true, message: 'Full test suite passed' };
    } catch (error: any) {
      return {
        passed: false,
        message: `Test suite failed: ${error.message}`
      };
    }
  }

  private async validateTraceability(): Promise<{ passed: boolean; message?: string }> {
    try {
      if (existsSync('scripts/verify/traceability.sh')) {
        execSync('bash scripts/verify/traceability.sh', { encoding: 'utf8', stdio: 'pipe' });
        return { passed: true, message: 'Traceability verification passed' };
      } else {
        return { passed: false, message: 'Traceability script not found' };
      }
    } catch (error) {
      return { passed: false, message: 'Traceability verification failed' };
    }
  }
}