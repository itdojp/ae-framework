/**
 * Enhanced Rust Formal Verification Agent
 * Phase 2 of Issue #33: Advanced Rust formal verification with Prusti, Kani, and CBMC
 */

import { execSync } from 'child_process';
import { readFileSync, existsSync, writeFileSync } from 'fs';
import * as path from 'path';

export interface RustVerificationRequest {
  projectPath: string;
  sourceFiles: RustSourceFile[];
  verificationTools: VerificationTool[];
  options: VerificationOptions;
}

export interface RustSourceFile {
  path: string;
  content: string;
  annotations?: RustAnnotation[];
}

export interface RustAnnotation {
  type: 'precondition' | 'postcondition' | 'invariant' | 'assert' | 'assume' | 'contract';
  line: number;
  content: string;
}

export type VerificationTool = 'prusti' | 'kani' | 'cbmc' | 'miri' | 'loom';

export interface VerificationOptions {
  timeout?: number; // in seconds
  memoryLimit?: number; // in MB
  unwindLimit?: number; // for CBMC
  strictMode?: boolean;
  generateReport?: boolean;
  checkOverflow?: boolean;
  checkConcurrency?: boolean;
}

export interface RustVerificationResult {
  tool: VerificationTool;
  success: boolean;
  results: VerificationCheck[];
  performance: PerformanceMetrics;
  report?: VerificationReport;
  errors: VerificationError[];
  warnings: VerificationWarning[];
}

export interface VerificationCheck {
  type: 'safety' | 'liveness' | 'functional' | 'memory' | 'concurrency';
  description: string;
  status: 'passed' | 'failed' | 'timeout' | 'unknown';
  location?: SourceLocation;
  details?: string;
  counterexample?: string;
}

export interface PerformanceMetrics {
  executionTime: number;
  memoryUsage: number;
  codeSize: number;
  verificationComplexity: 'low' | 'medium' | 'high' | 'very-high';
}

export interface VerificationReport {
  summary: string;
  statistics: {
    totalChecks: number;
    passedChecks: number;
    failedChecks: number;
    coverage: number;
  };
  recommendations: string[];
  toolSpecificResults: Record<string, any>;
}

export interface VerificationError {
  tool: VerificationTool;
  type: string;
  message: string;
  location?: SourceLocation;
  severity: 'critical' | 'error' | 'warning';
}

export interface VerificationWarning {
  tool: VerificationTool;
  type: string;
  message: string;
  location?: SourceLocation;
  suggestion?: string;
}

export interface SourceLocation {
  file: string;
  line: number;
  column: number;
  function?: string;
}

export class RustVerificationAgent {
  private installedTools: Set<VerificationTool> = new Set();

  constructor() {
    this.detectInstalledTools();
  }

  /**
   * Main verification entry point - runs multiple verification tools
   */
  async verifyRustProject(request: RustVerificationRequest): Promise<RustVerificationResult[]> {
    const results: RustVerificationResult[] = [];

    // Validate project structure
    await this.validateProjectStructure(request.projectPath);

    // Prepare project for verification (add annotations, setup config)
    await this.prepareProjectForVerification(request);

    // Run each requested verification tool
    for (const tool of request.verificationTools) {
      if (!this.installedTools.has(tool)) {
        results.push({
          tool,
          success: false,
          results: [],
          performance: { executionTime: 0, memoryUsage: 0, codeSize: 0, verificationComplexity: 'low' },
          errors: [{
            tool,
            type: 'tool_missing',
            message: `${tool} is not installed`,
            severity: 'error'
          }],
          warnings: []
        });
        continue;
      }

      try {
        const result = await this.runVerificationTool(tool, request);
        results.push(result);
      } catch (error) {
        results.push({
          tool,
          success: false,
          results: [],
          performance: { executionTime: 0, memoryUsage: 0, codeSize: 0, verificationComplexity: 'low' },
          errors: [{
            tool,
            type: 'execution_error',
            message: error instanceof Error ? error.message : 'Unknown error',
            severity: 'critical'
          }],
          warnings: []
        });
      }
    }

    // Generate combined report if requested
    if (request.options.generateReport) {
      await this.generateCombinedReport(results, request.projectPath);
    }

    return results;
  }

  /**
   * Run Prusti verification (Rust ownership and borrowing verification)
   */
  private async runPrustiVerification(request: RustVerificationRequest): Promise<RustVerificationResult> {
    const startTime = Date.now();
    const checks: VerificationCheck[] = [];
    const errors: VerificationError[] = [];
    const warnings: VerificationWarning[] = [];

    try {
      // Run Prusti verification
      const prustiCmd = `cd ${request.projectPath} && cargo prusti`;
      const output = execSync(prustiCmd, { 
        timeout: (request.options.timeout || 300) * 1000,
        encoding: 'utf8',
        maxBuffer: 10 * 1024 * 1024 // 10MB buffer
      });

      // Parse Prusti output
      const parsedResults = this.parsePrustiOutput(output);
      checks.push(...parsedResults.checks);
      warnings.push(...parsedResults.warnings);

      const executionTime = Date.now() - startTime;
      
      return {
        tool: 'prusti',
        success: parsedResults.checks.every(c => c.status === 'passed'),
        results: checks,
        performance: {
          executionTime,
          memoryUsage: this.estimateMemoryUsage(output),
          codeSize: this.calculateCodeSize(request.sourceFiles),
          verificationComplexity: this.assessComplexity(request.sourceFiles)
        },
        errors,
        warnings
      };

    } catch (error) {
      const executionTime = Date.now() - startTime;
      
      return {
        tool: 'prusti',
        success: false,
        results: checks,
        performance: {
          executionTime,
          memoryUsage: 0,
          codeSize: this.calculateCodeSize(request.sourceFiles),
          verificationComplexity: this.assessComplexity(request.sourceFiles)
        },
        errors: [{
          tool: 'prusti',
          type: 'execution_error',
          message: error instanceof Error ? error.message : 'Prusti verification failed',
          severity: 'error'
        }],
        warnings
      };
    }
  }

  /**
   * Run Kani verification (bounded model checking for Rust)
   */
  private async runKaniVerification(request: RustVerificationRequest): Promise<RustVerificationResult> {
    const startTime = Date.now();
    const checks: VerificationCheck[] = [];
    const errors: VerificationError[] = [];
    const warnings: VerificationWarning[] = [];

    try {
      // Build Kani command with options
      let kaniCmd = `cd ${request.projectPath} && cargo kani`;
      
      if (request.options.unwindLimit) {
        kaniCmd += ` --unwind ${request.options.unwindLimit}`;
      }
      
      if (request.options.checkOverflow) {
        kaniCmd += ` --overflow-checks`;
      }

      const output = execSync(kaniCmd, { 
        timeout: (request.options.timeout || 600) * 1000,
        encoding: 'utf8',
        maxBuffer: 20 * 1024 * 1024 // 20MB buffer
      });

      // Parse Kani output
      const parsedResults = this.parseKaniOutput(output);
      checks.push(...parsedResults.checks);
      warnings.push(...parsedResults.warnings);

      const executionTime = Date.now() - startTime;
      
      return {
        tool: 'kani',
        success: parsedResults.checks.every(c => c.status === 'passed'),
        results: checks,
        performance: {
          executionTime,
          memoryUsage: this.estimateMemoryUsage(output),
          codeSize: this.calculateCodeSize(request.sourceFiles),
          verificationComplexity: this.assessComplexity(request.sourceFiles)
        },
        errors,
        warnings
      };

    } catch (error) {
      const executionTime = Date.now() - startTime;
      
      return {
        tool: 'kani',
        success: false,
        results: checks,
        performance: {
          executionTime,
          memoryUsage: 0,
          codeSize: this.calculateCodeSize(request.sourceFiles),
          verificationComplexity: this.assessComplexity(request.sourceFiles)
        },
        errors: [{
          tool: 'kani',
          type: 'execution_error',
          message: error instanceof Error ? error.message : 'Kani verification failed',
          severity: 'error'
        }],
        warnings
      };
    }
  }

  /**
   * Run CBMC verification (bounded model checking)
   */
  private async runCBMCVerification(request: RustVerificationRequest): Promise<RustVerificationResult> {
    const startTime = Date.now();
    const checks: VerificationCheck[] = [];
    const errors: VerificationError[] = [];
    const warnings: VerificationWarning[] = [];

    try {
      // CBMC requires compilation to GOTO programs first
      const gotoCmd = `cd ${request.projectPath} && goto-cc -o program.goto src/*.rs`;
      execSync(gotoCmd, { encoding: 'utf8' });

      // Run CBMC
      let cbmcCmd = `cd ${request.projectPath} && cbmc program.goto`;
      
      if (request.options.unwindLimit) {
        cbmcCmd += ` --unwind ${request.options.unwindLimit}`;
      }
      
      if (request.options.strictMode) {
        cbmcCmd += ` --bounds-check --pointer-check --memory-leak-check`;
      }

      const output = execSync(cbmcCmd, { 
        timeout: (request.options.timeout || 1200) * 1000,
        encoding: 'utf8',
        maxBuffer: 50 * 1024 * 1024 // 50MB buffer
      });

      // Parse CBMC output
      const parsedResults = this.parseCBMCOutput(output);
      checks.push(...parsedResults.checks);
      warnings.push(...parsedResults.warnings);

      const executionTime = Date.now() - startTime;
      
      return {
        tool: 'cbmc',
        success: parsedResults.checks.every(c => c.status === 'passed'),
        results: checks,
        performance: {
          executionTime,
          memoryUsage: this.estimateMemoryUsage(output),
          codeSize: this.calculateCodeSize(request.sourceFiles),
          verificationComplexity: this.assessComplexity(request.sourceFiles)
        },
        errors,
        warnings
      };

    } catch (error) {
      const executionTime = Date.now() - startTime;
      
      return {
        tool: 'cbmc',
        success: false,
        results: checks,
        performance: {
          executionTime,
          memoryUsage: 0,
          codeSize: this.calculateCodeSize(request.sourceFiles),
          verificationComplexity: this.assessComplexity(request.sourceFiles)
        },
        errors: [{
          tool: 'cbmc',
          type: 'execution_error',
          message: error instanceof Error ? error.message : 'CBMC verification failed',
          severity: 'error'
        }],
        warnings
      };
    }
  }

  /**
   * Run Miri verification (interpreter for unsafe Rust)
   */
  private async runMiriVerification(request: RustVerificationRequest): Promise<RustVerificationResult> {
    const startTime = Date.now();
    const checks: VerificationCheck[] = [];
    const errors: VerificationError[] = [];
    const warnings: VerificationWarning[] = [];

    try {
      const miriCmd = `cd ${request.projectPath} && cargo miri test`;
      const output = execSync(miriCmd, { 
        timeout: (request.options.timeout || 600) * 1000,
        encoding: 'utf8'
      });

      // Parse Miri output
      const parsedResults = this.parseMiriOutput(output);
      checks.push(...parsedResults.checks);
      warnings.push(...parsedResults.warnings);

      const executionTime = Date.now() - startTime;
      
      return {
        tool: 'miri',
        success: parsedResults.checks.every(c => c.status === 'passed'),
        results: checks,
        performance: {
          executionTime,
          memoryUsage: this.estimateMemoryUsage(output),
          codeSize: this.calculateCodeSize(request.sourceFiles),
          verificationComplexity: this.assessComplexity(request.sourceFiles)
        },
        errors,
        warnings
      };

    } catch (error) {
      return {
        tool: 'miri',
        success: false,
        results: [],
        performance: {
          executionTime: Date.now() - startTime,
          memoryUsage: 0,
          codeSize: this.calculateCodeSize(request.sourceFiles),
          verificationComplexity: this.assessComplexity(request.sourceFiles)
        },
        errors: [{
          tool: 'miri',
          type: 'execution_error',
          message: error instanceof Error ? error.message : 'Miri verification failed',
          severity: 'error'
        }],
        warnings
      };
    }
  }

  /**
   * Detect installed verification tools
   */
  private detectInstalledTools(): void {
    const tools: VerificationTool[] = ['prusti', 'kani', 'cbmc', 'miri', 'loom'];
    
    for (const tool of tools) {
      try {
        switch (tool) {
          case 'prusti':
            execSync('cargo prusti --version', { stdio: 'pipe' });
            this.installedTools.add(tool);
            break;
          case 'kani':
            execSync('cargo kani --version', { stdio: 'pipe' });
            this.installedTools.add(tool);
            break;
          case 'cbmc':
            execSync('cbmc --version', { stdio: 'pipe' });
            this.installedTools.add(tool);
            break;
          case 'miri':
            execSync('cargo miri --version', { stdio: 'pipe' });
            this.installedTools.add(tool);
            break;
          case 'loom':
            // Loom is a library, check if it's in Cargo.toml
            // This is a simplified check
            this.installedTools.add(tool);
            break;
        }
      } catch {
        // Tool not available
      }
    }
  }

  // Private helper methods
  private async runVerificationTool(tool: VerificationTool, request: RustVerificationRequest): Promise<RustVerificationResult> {
    switch (tool) {
      case 'prusti':
        return this.runPrustiVerification(request);
      case 'kani':
        return this.runKaniVerification(request);
      case 'cbmc':
        return this.runCBMCVerification(request);
      case 'miri':
        return this.runMiriVerification(request);
      case 'loom':
        return this.runLoomVerification(request);
      default:
        throw new Error(`Unsupported verification tool: ${tool}`);
    }
  }

  private async runLoomVerification(request: RustVerificationRequest): Promise<RustVerificationResult> {
    // Loom verification for concurrency testing
    const startTime = Date.now();
    
    try {
      const loomCmd = `cd ${request.projectPath} && cargo test --features loom`;
      const output = execSync(loomCmd, { 
        timeout: (request.options.timeout || 300) * 1000,
        encoding: 'utf8'
      });

      const checks: VerificationCheck[] = [{
        type: 'concurrency',
        description: 'Loom concurrency verification',
        status: output.includes('test result: ok') ? 'passed' : 'failed',
        details: 'Concurrent data structure verification completed'
      }];

      return {
        tool: 'loom',
        success: output.includes('test result: ok'),
        results: checks,
        performance: {
          executionTime: Date.now() - startTime,
          memoryUsage: this.estimateMemoryUsage(output),
          codeSize: this.calculateCodeSize(request.sourceFiles),
          verificationComplexity: 'medium'
        },
        errors: [],
        warnings: []
      };

    } catch (error) {
      return {
        tool: 'loom',
        success: false,
        results: [],
        performance: {
          executionTime: Date.now() - startTime,
          memoryUsage: 0,
          codeSize: this.calculateCodeSize(request.sourceFiles),
          verificationComplexity: 'medium'
        },
        errors: [{
          tool: 'loom',
          type: 'execution_error',
          message: error instanceof Error ? error.message : 'Loom verification failed',
          severity: 'error'
        }],
        warnings: []
      };
    }
  }

  private async validateProjectStructure(projectPath: string): Promise<void> {
    const cargoTomlPath = path.join(projectPath, 'Cargo.toml');
    if (!existsSync(cargoTomlPath)) {
      throw new Error('Not a valid Rust project: Cargo.toml not found');
    }

    const srcPath = path.join(projectPath, 'src');
    if (!existsSync(srcPath)) {
      throw new Error('Not a valid Rust project: src directory not found');
    }
  }

  private async prepareProjectForVerification(request: RustVerificationRequest): Promise<void> {
    // Add verification dependencies to Cargo.toml if needed
    const cargoTomlPath = path.join(request.projectPath, 'Cargo.toml');
    let cargoContent = readFileSync(cargoTomlPath, 'utf8');

    // Add necessary dependencies for verification tools
    if (request.verificationTools.includes('loom') && !cargoContent.includes('loom')) {
      cargoContent += `\n[dependencies]\nloom = { version = "0.5", optional = true }\n`;
      cargoContent += `[features]\nloom = ["dep:loom"]\n`;
      writeFileSync(cargoTomlPath, cargoContent);
    }

    // Add verification annotations to source files if provided
    for (const sourceFile of request.sourceFiles) {
      if (sourceFile.annotations && sourceFile.annotations.length > 0) {
        await this.addAnnotationsToFile(sourceFile);
      }
    }
  }

  private async addAnnotationsToFile(sourceFile: RustSourceFile): Promise<void> {
    let content = sourceFile.content;
    const lines = content.split('\n');

    // Add annotations at specified lines
    for (const annotation of sourceFile.annotations || []) {
      const annotationText = this.formatAnnotation(annotation);
      lines.splice(annotation.line, 0, annotationText);
    }

    sourceFile.content = lines.join('\n');
    
    // Write back to file
    writeFileSync(sourceFile.path, sourceFile.content);
  }

  private formatAnnotation(annotation: RustAnnotation): string {
    switch (annotation.type) {
      case 'precondition':
        return `    // @pre: ${annotation.content}`;
      case 'postcondition':
        return `    // @post: ${annotation.content}`;
      case 'invariant':
        return `    // @invariant: ${annotation.content}`;
      case 'assert':
        return `    assert!(${annotation.content});`;
      case 'assume':
        return `    // assume: ${annotation.content}`;
      case 'contract':
        return `    // @contract: ${annotation.content}`;
      default:
        return `    // ${annotation.content}`;
    }
  }

  // Output parsers for different tools
  private parsePrustiOutput(output: string): { checks: VerificationCheck[]; warnings: VerificationWarning[] } {
    const checks: VerificationCheck[] = [];
    const warnings: VerificationWarning[] = [];

    const lines = output.split('\n');
    for (const line of lines) {
      if (line.includes('verification successful')) {
        checks.push({
          type: 'safety',
          description: 'Prusti ownership verification',
          status: 'passed'
        });
      } else if (line.includes('verification failed')) {
        checks.push({
          type: 'safety',
          description: 'Prusti ownership verification',
          status: 'failed',
          details: line
        });
      } else if (line.includes('warning:')) {
        warnings.push({
          tool: 'prusti',
          type: 'prusti_warning',
          message: line
        });
      }
    }

    if (checks.length === 0) {
      checks.push({
        type: 'safety',
        description: 'Prusti verification completed',
        status: output.includes('error') ? 'failed' : 'passed'
      });
    }

    return { checks, warnings };
  }

  private parseKaniOutput(output: string): { checks: VerificationCheck[]; warnings: VerificationWarning[] } {
    const checks: VerificationCheck[] = [];
    const warnings: VerificationWarning[] = [];

    const lines = output.split('\n');
    for (const line of lines) {
      if (line.includes('VERIFICATION SUCCESSFUL')) {
        checks.push({
          type: 'safety',
          description: 'Kani bounded model checking',
          status: 'passed'
        });
      } else if (line.includes('VERIFICATION FAILED')) {
        checks.push({
          type: 'safety',
          description: 'Kani bounded model checking',
          status: 'failed',
          details: line
        });
      } else if (line.includes('assertion failed')) {
        checks.push({
          type: 'functional',
          description: 'Assertion check',
          status: 'failed',
          details: line
        });
      }
    }

    if (checks.length === 0) {
      checks.push({
        type: 'safety',
        description: 'Kani verification completed',
        status: output.includes('FAILED') ? 'failed' : 'passed'
      });
    }

    return { checks, warnings };
  }

  private parseCBMCOutput(output: string): { checks: VerificationCheck[]; warnings: VerificationWarning[] } {
    const checks: VerificationCheck[] = [];
    const warnings: VerificationWarning[] = [];

    const lines = output.split('\n');
    for (const line of lines) {
      if (line.includes('VERIFICATION SUCCESSFUL')) {
        checks.push({
          type: 'safety',
          description: 'CBMC model checking',
          status: 'passed'
        });
      } else if (line.includes('VERIFICATION FAILED')) {
        checks.push({
          type: 'safety',
          description: 'CBMC model checking',
          status: 'failed',
          details: line
        });
      } else if (line.includes('assertion failed')) {
        checks.push({
          type: 'functional',
          description: 'Assertion violation',
          status: 'failed',
          details: line
        });
      }
    }

    if (checks.length === 0) {
      checks.push({
        type: 'safety',
        description: 'CBMC verification completed',
        status: output.includes('FAILED') ? 'failed' : 'passed'
      });
    }

    return { checks, warnings };
  }

  private parseMiriOutput(output: string): { checks: VerificationCheck[]; warnings: VerificationWarning[] } {
    const checks: VerificationCheck[] = [];
    const warnings: VerificationWarning[] = [];

    if (output.includes('test result: ok')) {
      checks.push({
        type: 'memory',
        description: 'Miri undefined behavior detection',
        status: 'passed'
      });
    } else if (output.includes('error:')) {
      checks.push({
        type: 'memory',
        description: 'Miri undefined behavior detection',
        status: 'failed',
        details: output
      });
    }

    return { checks, warnings };
  }

  // Utility methods
  private estimateMemoryUsage(output: string): number {
    // Simple heuristic based on output size
    return Math.max(output.length / 1000, 10); // MB estimate
  }

  private calculateCodeSize(sourceFiles: RustSourceFile[]): number {
    return sourceFiles.reduce((total, file) => total + file.content.length, 0);
  }

  private assessComplexity(sourceFiles: RustSourceFile[]): 'low' | 'medium' | 'high' | 'very-high' {
    const totalSize = this.calculateCodeSize(sourceFiles);
    const fileCount = sourceFiles.length;
    
    if (totalSize < 5000 && fileCount <= 5) return 'low';
    if (totalSize < 20000 && fileCount <= 15) return 'medium';
    if (totalSize < 100000 && fileCount <= 50) return 'high';
    return 'very-high';
  }

  private async generateCombinedReport(results: RustVerificationResult[], projectPath: string): Promise<void> {
    const report = {
      timestamp: new Date().toISOString(),
      projectPath,
      overallSuccess: results.every(r => r.success),
      toolResults: results,
      summary: this.generateSummary(results)
    };

    const reportPath = path.join(projectPath, 'verification-report.json');
    writeFileSync(reportPath, JSON.stringify(report, null, 2));
  }

  private generateSummary(results: RustVerificationResult[]): string {
    const totalChecks = results.reduce((sum, r) => sum + r.results.length, 0);
    const passedChecks = results.reduce((sum, r) => sum + r.results.filter(c => c.status === 'passed').length, 0);
    const failedChecks = totalChecks - passedChecks;

    return `Verification completed: ${passedChecks}/${totalChecks} checks passed, ${failedChecks} failed. ` +
           `Tools used: ${results.map(r => r.tool).join(', ')}.`;
  }

  /**
   * Get list of available verification tools
   */
  getAvailableTools(): VerificationTool[] {
    return Array.from(this.installedTools);
  }

  /**
   * Check if a specific tool is available
   */
  isToolAvailable(tool: VerificationTool): boolean {
    return this.installedTools.has(tool);
  }
}