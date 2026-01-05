/**
 * Phase 1: Codebase Analysis using NaturalLanguageTaskAdapter
 * 
 * This module performs a comprehensive analysis of the ae-framework codebase
 * using the natural language processing capabilities to identify patterns,
 * issues, and improvement opportunities.
 */

import { NaturalLanguageTaskAdapter } from '../agents/natural-language-task-adapter.js';
import type { TaskRequest } from '../agents/task-types.js';
import * as fs from 'fs/promises';
import * as path from 'path';

export interface CodebaseAnalysisResult {
  summary: string;
  analysis: string;
  recommendations: string[];
  nextActions: string[];
  warnings: string[];
  shouldBlockProgress: boolean;
  typeScriptErrors: number;
  testCoverage: {
    files: number;
    coverage: number;
  };
  codeQuality: {
    score: number;
    issues: string[];
  };
}

export class CodebaseAnalyzer {
  private adapter: NaturalLanguageTaskAdapter;

  constructor() {
    this.adapter = new NaturalLanguageTaskAdapter();
  }

  /**
   * Perform comprehensive analysis of the ae-framework codebase
   */
  async analyzeCodebase(): Promise<CodebaseAnalysisResult> {
    const tsErrors = await this.countTypeScriptErrors();
    const testStats = await this.analyzeTestCoverage();
    const qualityIssues = await this.analyzeCodeQuality();
    
    const codebaseRequirements = await this.extractCodebaseRequirements();
    
    const analysisRequest: TaskRequest = {
      description: 'Analyze ae-framework codebase requirements',
      prompt: `
# ae-framework Codebase Analysis Request

Please analyze the following codebase characteristics and requirements:

## Current State
- TypeScript compilation errors: ${tsErrors}
- Test files count: ${testStats.files}
- Estimated test coverage: ${testStats.coverage}%
- Code quality issues identified: ${qualityIssues.length}

## Requirements Analysis Needed
${codebaseRequirements}

## Specific Analysis Goals
1. Identify architectural patterns and consistency
2. Analyze requirement completeness for framework components
3. Detect gaps in component integration
4. Assess technical debt and maintainability
5. Validate framework design principles adherence

Please provide recommendations for improving code quality, resolving TypeScript errors, and enhancing the overall framework architecture.
      `,
      subagent_type: 'general-purpose',
      context: {
        domain: 'software-framework',
        projectScope: 'ai-agent-enabled-framework',
        codebase: 'typescript-nodejs'
      }
    };

    const analysisResult = await this.adapter.handleNaturalLanguageTask(analysisRequest);

    return {
      summary: analysisResult.summary,
      analysis: analysisResult.analysis,
      recommendations: analysisResult.recommendations,
      nextActions: analysisResult.nextActions,
      warnings: analysisResult.warnings,
      shouldBlockProgress: analysisResult.shouldBlockProgress,
      typeScriptErrors: tsErrors,
      testCoverage: testStats,
      codeQuality: {
        score: Math.max(0, 100 - qualityIssues.length * 5), // Simple scoring
        issues: qualityIssues
      }
    };
  }

  /**
   * Count TypeScript compilation errors by running tsc
   */
  private async countTypeScriptErrors(): Promise<number> {
    try {
      const { execSync } = await import('child_process');
      execSync('npm run build', { 
        encoding: 'utf-8',
        cwd: process.cwd(),
        stdio: 'pipe'
      });
      return 0; // No errors if build succeeds
    } catch (error: any) {
      const errorOutput = error.stdout || error.stderr || '';
      const errorMatches = errorOutput.match(/error TS\d+:/g);
      return errorMatches ? errorMatches.length : 0;
    }
  }

  /**
   * Analyze test coverage by counting test files and estimating coverage
   */
  private async analyzeTestCoverage(): Promise<{ files: number; coverage: number }> {
    try {
      const testFiles = await this.findTestFiles();
      const sourceFiles = await this.findSourceFiles();
      
      const coverage = sourceFiles.length > 0 
        ? Math.round((testFiles.length / sourceFiles.length) * 100)
        : 0;

      return {
        files: testFiles.length,
        coverage: Math.min(coverage, 100) // Cap at 100%
      };
    } catch (error) {
      return { files: 0, coverage: 0 };
    }
  }

  /**
   * Analyze code quality by identifying common issues
   */
  private async analyzeCodeQuality(): Promise<string[]> {
    const issues: string[] = [];
    
    try {
      // Check for common anti-patterns in TypeScript files
      const sourceFiles = await this.findSourceFiles();
      
      for (const file of sourceFiles.slice(0, 10)) { // Sample first 10 files
        try {
          const content = await fs.readFile(file, 'utf-8');
          
          if (content.includes('any')) {
            issues.push(`Use of 'any' type in ${path.basename(file)}`);
          }
          
          if (content.includes('ts-ignore')) {
            issues.push(`TypeScript ignore directive in ${path.basename(file)}`);
          }
          
          if (content.includes('console.log')) {
            issues.push(`Console.log statement in ${path.basename(file)}`);
          }
          
          if (content.length > 1000 && !content.includes('/**')) {
            issues.push(`Large file without documentation: ${path.basename(file)}`);
          }
        } catch (fileError) {
          // Skip files that can't be read
        }
      }
    } catch (error) {
      issues.push('Could not analyze source files for quality issues');
    }
    
    return issues;
  }

  /**
   * Extract requirements-like statements from the codebase
   */
  private async extractCodebaseRequirements(): Promise<string> {
    const requirements: string[] = [
      // Framework-level requirements
      "The system must provide AI agent integration capabilities",
      "The framework should support TypeScript for type safety",
      "The system must include comprehensive testing infrastructure",
      "The framework should provide state management utilities",
      "The system must support container orchestration",
      "The framework should include quality gates and validation",
      "The system must provide TDD capabilities",
      "The framework should support benchmark integration",
      "The system must include security analysis tools",
      "The framework should provide formal specification support",
      
      // Technical requirements from codebase analysis
      "All TypeScript compilation errors must be resolved",
      "Test coverage should be above 80%",
      "Code quality should follow established patterns",
      "Dependencies should be properly managed",
      "Documentation should be comprehensive",
      "Performance should meet established benchmarks",
      "Security vulnerabilities must be addressed",
      "Integration points must be well-defined",
      "Error handling must be consistent",
      "Logging and monitoring must be integrated"
    ];
    
    return requirements.join('\n');
  }

  /**
   * Find all test files in the project
   */
  private async findTestFiles(): Promise<string[]> {
    const testFiles: string[] = [];
    
    async function searchDirectory(dir: string): Promise<void> {
      try {
        const entries = await fs.readdir(dir, { withFileTypes: true });
        
        for (const entry of entries) {
          const fullPath = path.join(dir, entry.name);
          
          if (entry.isDirectory() && !entry.name.startsWith('.') && entry.name !== 'node_modules') {
            await searchDirectory(fullPath);
          } else if (entry.isFile() && 
                    (entry.name.endsWith('.test.ts') || 
                     entry.name.endsWith('.test.js') || 
                     entry.name.endsWith('.spec.ts') || 
                     entry.name.endsWith('.spec.js'))) {
            testFiles.push(fullPath);
          }
        }
      } catch (error) {
        // Skip directories that can't be read
      }
    }
    
    await searchDirectory(process.cwd());
    return testFiles;
  }

  /**
   * Find all source files in the project
   */
  private async findSourceFiles(): Promise<string[]> {
    const sourceFiles: string[] = [];
    
    async function searchDirectory(dir: string): Promise<void> {
      try {
        const entries = await fs.readdir(dir, { withFileTypes: true });
        
        for (const entry of entries) {
          const fullPath = path.join(dir, entry.name);
          
          if (entry.isDirectory() && 
              !entry.name.startsWith('.') && 
              entry.name !== 'node_modules' && 
              entry.name !== 'dist' && 
              entry.name !== 'coverage') {
            await searchDirectory(fullPath);
          } else if (entry.isFile() && 
                    (entry.name.endsWith('.ts') || entry.name.endsWith('.js')) &&
                    !entry.name.endsWith('.test.ts') &&
                    !entry.name.endsWith('.test.js') &&
                    !entry.name.endsWith('.spec.ts') &&
                    !entry.name.endsWith('.spec.js') &&
                    !entry.name.endsWith('.d.ts')) {
            sourceFiles.push(fullPath);
          }
        }
      } catch (error) {
        // Skip directories that can't be read
      }
    }
    
    await searchDirectory(path.join(process.cwd(), 'src'));
    return sourceFiles;
  }

  /**
   * Generate detailed report from analysis results
   */
  generateReport(results: CodebaseAnalysisResult): string {
    return `
# ae-framework Codebase Analysis Report

## Executive Summary
${results.summary}

## Detailed Analysis
${results.analysis}

## Key Metrics
- **TypeScript Errors**: ${results.typeScriptErrors}
- **Test Files**: ${results.testCoverage.files}
- **Estimated Coverage**: ${results.testCoverage.coverage}%
- **Code Quality Score**: ${results.codeQuality.score}/100

## Code Quality Issues
${results.codeQuality.issues.map(issue => `- ${issue}`).join('\n')}

## Recommendations
${results.recommendations.map(rec => `- ${rec}`).join('\n')}

## Next Actions
${results.nextActions.map(action => `- ${action}`).join('\n')}

## Warnings
${results.warnings.map(warning => `- ⚠️ ${warning}`).join('\n')}

## Progress Status
${results.shouldBlockProgress ? '🔴 **BLOCKED**: Critical issues must be resolved before proceeding' : '🟢 **READY**: Can proceed to next phase'}

---
*Generated by ae-framework Phase 1 Codebase Analysis*
    `.trim();
  }
}

export default CodebaseAnalyzer;
