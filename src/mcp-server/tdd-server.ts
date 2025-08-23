#!/usr/bin/env node

import { Server } from '@modelcontextprotocol/sdk/server/index.js';
import { StdioServerTransport } from '@modelcontextprotocol/sdk/server/stdio.js';
import {
  CallToolRequestSchema,
  ListToolsRequestSchema,
} from '@modelcontextprotocol/sdk/types.js';
import { execSync } from 'child_process';
import { existsSync, readFileSync } from 'fs';
import { glob } from 'glob';

interface TDDViolation {
  type: 'missing_test' | 'failing_test' | 'skip_red' | 'low_coverage';
  severity: 'error' | 'warning';
  file?: string;
  message: string;
  suggestion: string;
}

interface TDDAnalysis {
  phase: string;
  violations: TDDViolation[];
  recommendations: string[];
  nextAction: string;
  canProceed: boolean;
}

class TDDGuardServer {
  private server: Server;

  constructor() {
    this.server = new Server(
      {
        name: 'tdd-guard',
        version: '1.0.0',
      },
      {
        capabilities: {
          tools: {},
        },
      }
    );

    this.setupToolHandlers();
  }

  private setupToolHandlers() {
    this.server.setRequestHandler(ListToolsRequestSchema, async () => ({
      tools: [
        {
          name: 'analyze_tdd_compliance',
          description: 'Analyze current project for TDD compliance and violations',
          inputSchema: {
            type: 'object',
            properties: {
              path: {
                type: 'string',
                description: 'Project path to analyze (defaults to current directory)',
              },
              phase: {
                type: 'string',
                description: 'Current development phase (1-intent, 2-formal, 3-tests, 4-code, 5-verify, 6-operate)',
              },
            },
          },
        },
        {
          name: 'guide_tdd_development',
          description: 'Provide step-by-step TDD guidance for a specific feature',
          inputSchema: {
            type: 'object',
            properties: {
              feature: {
                type: 'string',
                description: 'Feature to implement (e.g., "user authentication")',
              },
              currentStep: {
                type: 'string',
                description: 'Current step in development',
              },
            },
            required: ['feature'],
          },
        },
        {
          name: 'validate_test_first',
          description: 'Validate that tests are written before implementation',
          inputSchema: {
            type: 'object',
            properties: {
              sourceFiles: {
                type: 'array',
                items: { type: 'string' },
                description: 'Source files to validate',
              },
            },
          },
        },
        {
          name: 'check_red_green_cycle',
          description: 'Verify proper RED-GREEN-REFACTOR cycle compliance',
          inputSchema: {
            type: 'object',
            properties: {
              testCommand: {
                type: 'string',
                description: 'Command to run tests (defaults to "npm test")',
              },
              expectRed: {
                type: 'boolean',
                description: 'Whether tests should be failing (RED phase)',
              },
            },
          },
        },
        {
          name: 'suggest_test_structure',
          description: 'Suggest test structure for a given implementation',
          inputSchema: {
            type: 'object',
            properties: {
              codeFile: {
                type: 'string',
                description: 'Path to code file to analyze',
              },
              framework: {
                type: 'string',
                description: 'Testing framework (vitest, jest, mocha, etc.)',
                default: 'vitest',
              },
            },
            required: ['codeFile'],
          },
        },
      ],
    }));

    this.server.setRequestHandler(CallToolRequestSchema, async (request) => {
      const { name, arguments: args } = request.params;

      switch (name) {
        case 'analyze_tdd_compliance':
          return this.analyzeTDDCompliance(args);
        
        case 'guide_tdd_development':
          return this.guideTDDDevelopment(args);
        
        case 'validate_test_first':
          return this.validateTestFirst(args);
        
        case 'check_red_green_cycle':
          return this.checkRedGreenCycle(args);
        
        case 'suggest_test_structure':
          return this.suggestTestStructure(args);
        
        default:
          throw new Error(`Unknown tool: ${name}`);
      }
    });
  }

  private async analyzeTDDCompliance(args: any): Promise<{ content: { type: 'text'; text: string }[] }> {
    const path = args.path || process.cwd();
    const phase = args.phase || this.detectCurrentPhase();

    const analysis: TDDAnalysis = {
      phase,
      violations: [],
      recommendations: [],
      nextAction: '',
      canProceed: true,
    };

    // Check for source files without tests
    const srcFiles = await glob('src/**/*.ts', { cwd: path });
    const testFiles = await glob('tests/**/*.test.ts', { cwd: path });

    for (const srcFile of srcFiles) {
      if (srcFile.includes('index.ts') || srcFile.includes('/types.ts')) continue;
      
      const baseName = srcFile.replace('src/', '').replace('.ts', '');
      const hasTest = testFiles.some(testFile => testFile.includes(baseName));
      
      if (!hasTest) {
        analysis.violations.push({
          type: 'missing_test',
          severity: 'error',
          file: srcFile,
          message: `No test file found for ${srcFile}`,
          suggestion: `Create tests/${baseName}.test.ts with comprehensive test cases`,
        });
      }
    }

    // Check test execution status
    try {
      execSync('npm test --silent', { stdio: 'pipe' });
      
      if (phase === '3-tests') {
        analysis.violations.push({
          type: 'skip_red',
          severity: 'warning',
          message: 'Tests are passing but should be RED in test-first phase',
          suggestion: 'Verify that tests fail initially to confirm they test the right behavior',
        });
      }
    } catch (error) {
      if (phase === '4-code') {
        analysis.violations.push({
          type: 'failing_test',
          severity: 'error',
          message: 'Tests are failing but should pass after implementation',
          suggestion: 'Implement the minimum code required to make tests pass',
        });
      }
    }

    // Generate recommendations
    analysis.recommendations = this.generateRecommendations(analysis.violations, phase);
    analysis.nextAction = this.determineNextAction(analysis.violations, phase);
    analysis.canProceed = analysis.violations.filter(v => v.severity === 'error').length === 0;

    const report = this.formatAnalysisReport(analysis);
    
    return {
      content: [{ type: 'text', text: report }],
    };
  }

  private async guideTDDDevelopment(args: any): Promise<{ content: { type: 'text'; text: string }[] }> {
    const { feature, currentStep } = args;
    
    const guidance = this.generateTDDGuidance(feature, currentStep);
    
    return {
      content: [{ type: 'text', text: guidance }],
    };
  }

  private async validateTestFirst(args: any): Promise<{ content: { type: 'text'; text: string }[] }> {
    const sourceFiles = args.sourceFiles || [];
    const violations: string[] = [];
    
    for (const srcFile of sourceFiles) {
      if (!existsSync(srcFile)) {
        continue;
      }
      
      // Check if corresponding test exists
      const baseName = srcFile.replace(/^src\//, '').replace(/\.ts$/, '');
      const possibleTestFiles = [
        `tests/${baseName}.test.ts`,
        `tests/${baseName}.spec.ts`,
        `__tests__/${baseName}.test.ts`,
      ];
      
      const hasTest = possibleTestFiles.some(testFile => existsSync(testFile));
      
      if (!hasTest) {
        violations.push(`${srcFile} has no corresponding test file`);
      }
    }
    
    const result = violations.length === 0 
      ? '✅ All source files have corresponding tests'
      : `❌ Test-first violations:\n${violations.map(v => `  • ${v}`).join('\n')}`;
    
    return {
      content: [{ type: 'text', text: result }],
    };
  }

  private async checkRedGreenCycle(args: any): Promise<{ content: { type: 'text'; text: string }[] }> {
    const testCommand = args.testCommand || 'npm test';
    const expectRed = args.expectRed || false;
    
    try {
      const result = execSync(`${testCommand} --silent`, { encoding: 'utf8', stdio: 'pipe' });
      
      if (expectRed) {
        return {
          content: [{
            type: 'text',
            text: '⚠️ Tests are GREEN but should be RED in test-first phase. Ensure tests fail initially to validate they test the intended behavior.',
          }],
        };
      } else {
        return {
          content: [{
            type: 'text',
            text: '✅ Tests are GREEN - implementation successfully makes tests pass!',
          }],
        };
      }
    } catch (error: any) {
      const output = error.stdout || error.stderr || '';
      
      if (expectRed) {
        return {
          content: [{
            type: 'text',
            text: '✅ Tests are RED as expected in test-first phase. Ready to implement code to make them pass.',
          }],
        };
      } else {
        return {
          content: [{
            type: 'text',
            text: `❌ Tests are failing:\n${output.split('\n').slice(-5).join('\n')}\n\nImplement the minimal code needed to make tests pass.`,
          }],
        };
      }
    }
  }

  private async suggestTestStructure(args: any): Promise<{ content: { type: 'text'; text: string }[] }> {
    const { codeFile, framework = 'vitest' } = args;
    
    if (!existsSync(codeFile)) {
      return {
        content: [{
          type: 'text',
          text: `❌ Code file ${codeFile} not found`,
        }],
      };
    }
    
    const codeContent = readFileSync(codeFile, 'utf8');
    const suggestion = this.generateTestSuggestion(codeContent, codeFile, framework);
    
    return {
      content: [{ type: 'text', text: suggestion }],
    };
  }

  private detectCurrentPhase(): string {
    // Detect phase based on existing artifacts
    if (existsSync('src') && existsSync('tests')) {
      return '4-code';
    } else if (existsSync('tests') || existsSync('specs')) {
      return '3-tests';
    } else if (existsSync('specs/formal')) {
      return '2-formal';
    } else {
      return '1-intent';
    }
  }

  private generateRecommendations(violations: TDDViolation[], phase: string): string[] {
    const recommendations: string[] = [];
    
    const missingTests = violations.filter(v => v.type === 'missing_test');
    if (missingTests.length > 0) {
      recommendations.push(`Write ${missingTests.length} missing test files before implementing code`);
    }
    
    const failingTests = violations.filter(v => v.type === 'failing_test');
    if (failingTests.length > 0) {
      recommendations.push('Fix failing tests by implementing the minimal code required');
    }
    
    if (phase === '3-tests' && violations.some(v => v.type === 'skip_red')) {
      recommendations.push('Verify tests fail initially (RED phase) before implementation');
    }
    
    return recommendations;
  }

  private determineNextAction(violations: TDDViolation[], phase: string): string {
    const errorViolations = violations.filter(v => v.severity === 'error');
    
    if (errorViolations.length > 0) {
      return `Fix ${errorViolations.length} TDD violations before proceeding`;
    }
    
    switch (phase) {
      case '1-intent':
        return 'Create formal specifications in specs/formal/';
      case '2-formal':
        return 'Write tests first (RED phase) in tests/';
      case '3-tests':
        return 'Implement minimal code to make tests pass (GREEN phase)';
      case '4-code':
        return 'Run verification tests and check coverage';
      case '5-verify':
        return 'Prepare operational deployment configuration';
      case '6-operate':
        return 'All phases complete - ready for production';
      default:
        return 'Continue with current development phase';
    }
  }

  private formatAnalysisReport(analysis: TDDAnalysis): string {
    const { phase, violations, recommendations, nextAction, canProceed } = analysis;
    
    let report = `# TDD Compliance Analysis\n\n`;
    report += `**Current Phase**: ${phase}\n`;
    report += `**Status**: ${canProceed ? '✅ Can proceed' : '❌ Violations must be fixed'}\n\n`;
    
    if (violations.length > 0) {
      report += `## 🚨 Violations Found (${violations.length})\n\n`;
      violations.forEach((violation, i) => {
        const icon = violation.severity === 'error' ? '❌' : '⚠️';
        report += `${i + 1}. ${icon} **${violation.type}**: ${violation.message}\n`;
        if (violation.file) {
          report += `   📁 File: ${violation.file}\n`;
        }
        report += `   💡 Suggestion: ${violation.suggestion}\n\n`;
      });
    } else {
      report += `## ✅ No TDD Violations Found\n\n`;
    }
    
    if (recommendations.length > 0) {
      report += `## 📋 Recommendations\n\n`;
      recommendations.forEach((rec, i) => {
        report += `${i + 1}. ${rec}\n`;
      });
      report += '\n';
    }
    
    report += `## 🎯 Next Action\n\n${nextAction}\n`;
    
    return report;
  }

  private generateTDDGuidance(feature: string, currentStep?: string): string {
    let guidance = `# TDD Guidance for: ${feature}\n\n`;
    
    if (!currentStep || currentStep === 'start') {
      guidance += `## 🚀 Starting TDD Development\n\n`;
      guidance += `1. **Write Test First (RED)**\n`;
      guidance += `   - Create test file for ${feature}\n`;
      guidance += `   - Define expected behavior in tests\n`;
      guidance += `   - Run tests to confirm they FAIL\n\n`;
      guidance += `2. **Implement Code (GREEN)**\n`;
      guidance += `   - Write minimal code to make tests pass\n`;
      guidance += `   - Run tests to confirm they PASS\n\n`;
      guidance += `3. **Refactor**\n`;
      guidance += `   - Improve code quality while keeping tests green\n\n`;
      guidance += `## 📝 Test Template\n\n`;
      guidance += `\`\`\`typescript\n`;
      guidance += `import { describe, it, expect } from 'vitest';\n\n`;
      guidance += `describe('${feature}', () => {\n`;
      guidance += `  it('should [behavior description]', () => {\n`;
      guidance += `    // Arrange\n`;
      guidance += `    // Act  \n`;
      guidance += `    // Assert\n`;
      guidance += `    expect(result).toBe(expected);\n`;
      guidance += `  });\n`;
      guidance += `});\n`;
      guidance += `\`\`\`\n`;
    }
    
    return guidance;
  }

  private generateTestSuggestion(codeContent: string, codeFile: string, framework: string): string {
    // Analyze code and suggest test structure
    const functions = this.extractFunctions(codeContent);
    const classes = this.extractClasses(codeContent);
    
    let suggestion = `# Test Suggestions for ${codeFile}\n\n`;
    
    if (functions.length > 0) {
      suggestion += `## Functions to Test\n\n`;
      functions.forEach(func => {
        suggestion += `### ${func}\n`;
        suggestion += `- Test happy path\n`;
        suggestion += `- Test edge cases\n`;
        suggestion += `- Test error conditions\n\n`;
      });
    }
    
    if (classes.length > 0) {
      suggestion += `## Classes to Test\n\n`;
      classes.forEach(cls => {
        suggestion += `### ${cls}\n`;
        suggestion += `- Test constructor\n`;
        suggestion += `- Test public methods\n`;
        suggestion += `- Test state changes\n\n`;
      });
    }
    
    return suggestion;
  }

  private extractFunctions(code: string): string[] {
    const functionRegex = /export\s+(?:async\s+)?function\s+(\w+)/g;
    const functions: string[] = [];
    let match;
    
    while ((match = functionRegex.exec(code)) !== null) {
      functions.push(match[1]!);
    }
    
    return functions;
  }

  private extractClasses(code: string): string[] {
    const classRegex = /export\s+class\s+(\w+)/g;
    const classes: string[] = [];
    let match;
    
    while ((match = classRegex.exec(code)) !== null) {
      if (match[1]) {
        classes.push(match[1]);
      }
    }
    
    return classes;
  }

  async run() {
    const transport = new StdioServerTransport();
    await this.server.connect(transport);
  }
}

const server = new TDDGuardServer();
server.run().catch(console.error);