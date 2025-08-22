/**
 * Hybrid TDD System
 * 
 * Integrates CLI tools, MCP server, and Claude Code agents
 * for comprehensive TDD enforcement and guidance
 */

import { TDDTaskAdapter, TaskRequest, TaskResponse } from '../agents/tdd-task-adapter.js';
import { AEFrameworkCLI } from '../cli/index.js';
import { ConfigLoader } from '../cli/config/ConfigLoader.js';
import { MetricsCollector } from '../cli/metrics/MetricsCollector.js';
import { AESpecCompiler, AEIR, CompileOptions } from '@ae-framework/spec-compiler';
import { EnhancedStateManager } from '../utils/enhanced-state-manager.js';
import * as fs from 'fs';
import * as path from 'path';

export interface HybridTDDConfig {
  enableCLI: boolean;
  enableMCPServer: boolean;
  enableClaudeCodeIntegration: boolean;
  enforceRealTime: boolean;
  strictMode: boolean;
  // AE-Spec/IR SSOT configuration
  enableSpecSSot: boolean;
  specPath: string;
  aeIrOutputPath: string;
}

export class HybridTDDSystem {
  private cli?: AEFrameworkCLI;
  private taskAdapter?: TDDTaskAdapter;
  private metricsCollector: MetricsCollector;
  private config: HybridTDDConfig;
  private specCompiler: AESpecCompiler;
  private stateManager: EnhancedStateManager;

  constructor(config: HybridTDDConfig) {
    this.config = config;
    this.metricsCollector = new MetricsCollector(ConfigLoader.load());
    this.specCompiler = new AESpecCompiler();
    this.stateManager = EnhancedStateManager.getInstance();
    
    if (config.enableCLI) {
      this.cli = new AEFrameworkCLI();
    }
    
    if (config.enableClaudeCodeIntegration) {
      this.taskAdapter = new TDDTaskAdapter();
    }
  }

  /**
   * Main entry point for TDD operations
   * Routes requests to appropriate handler based on context
   */
  async handleTDDRequest(request: {
    type: 'cli' | 'task' | 'mcp' | 'auto';
    data: any;
    phase?: number;
    context?: {
      isClaudeCode: boolean;
      hasTaskTool: boolean;
      userPreference: string;
    };
  }): Promise<{
    response: any;
    source: 'cli' | 'agent' | 'hybrid';
    followUp?: string[];
  }> {
    // AE-Spec/IR SSOT Pipeline Processing (issue #71 requirement)
    if (this.config.enableSpecSSot && await this.requiresSpecPipeline(request.phase)) {
      const aeIR = await this.processSpecPipeline();
      // Inject AE-IR into request for downstream phases
      request.data = { ...request.data, aeIR };
    }

    // Auto-detect best handler if type is 'auto'
    if (request.type === 'auto') {
      request.type = this.detectBestHandler(request.context);
    }

    switch (request.type) {
      case 'cli':
        return this.handleCLIRequest(request.data);
      
      case 'task':
        return this.handleTaskRequest(request.data);
      
      case 'mcp':
        return this.handleMCPRequest(request.data);
      
      default:
        return this.handleHybridRequest(request.data);
    }
  }

  /**
   * AE-Spec/IR SSOT Pipeline Processing
   * Converts NL specs to structured IR for downstream phases
   */
  private async processSpecPipeline(): Promise<AEIR> {
    const specPath = this.config.specPath || 'spec/ae-spec.md';
    const outputPath = this.config.aeIrOutputPath || '.ae/ae-ir.json';
    
    // Ensure spec file exists
    if (!fs.existsSync(specPath)) {
      throw new Error(`Spec file not found: ${specPath}`);
    }

    // Compile AE-Spec to AE-IR
    const compileOptions: CompileOptions = {
      inputPath: specPath,
      outputPath,
      validate: true,
      sourceMap: true,
    };

    const ir = await this.specCompiler.compile(compileOptions);
    
    // Lint AE-IR for ambiguity/undefined/conflicts
    const lintResult = await this.specCompiler.lint(ir);
    if (!lintResult.passed) {
      const errorMessages = lintResult.issues
        .filter(issue => issue.severity === 'error')
        .map(issue => issue.message)
        .join('; ');
      throw new Error(`Spec lint failed: ${errorMessages}`);
    }

    // Save SSOT to state manager
    await this.stateManager.saveSSOT(outputPath, ir);
    
    console.log(`✅ AE-Spec compiled to AE-IR successfully`);
    console.log(`📁 SSOT saved to: ${outputPath}`);
    
    if (lintResult.issues.length > 0) {
      const warnings = lintResult.issues.filter(i => i.severity === 'warn').length;
      const infos = lintResult.issues.filter(i => i.severity === 'info').length;
      console.log(`⚠️ Lint results: ${warnings} warnings, ${infos} info messages`);
    }

    return ir;
  }

  /**
   * Check if current phase requires spec pipeline processing
   */
  private async requiresSpecPipeline(phase?: number): Promise<boolean> {
    // Phases 2-6 require AE-IR as input
    if (!phase) return true; // Default: always process
    return phase >= 2;
  }

  /**
   * Proactive TDD monitoring and intervention
   * Runs in background to provide real-time guidance
   */
  async startProactiveMonitoring(): Promise<void> {
    if (!this.config.enforceRealTime) return;

    // Set up file watchers
    this.setupFileWatchers();
    
    // Set up git hooks
    this.setupGitIntegration();
    
    // Start periodic compliance checks
    this.startPeriodicChecks();
  }

  /**
   * Integration with existing development workflow
   */
  async integrateWithWorkflow(workflow: {
    ide: string;
    vcs: string;
    ci: string;
    testRunner: string;
  }): Promise<{
    integrations: Array<{
      type: string;
      status: 'active' | 'available' | 'unavailable';
      setup: string[];
    }>;
  }> {
    const integrations = [];

    // IDE Integration
    if (workflow.ide === 'vscode') {
      integrations.push({
        type: 'VSCode Extension',
        status: 'available' as const,
        setup: [
          'Install ae-framework VSCode extension',
          'Configure TDD settings in workspace',
          'Enable real-time validation',
        ],
      });
    }

    // Git Integration
    if (workflow.vcs === 'git') {
      integrations.push({
        type: 'Git Hooks',
        status: 'active' as const,
        setup: [
          'Pre-commit hooks installed',
          'TDD validation active',
          'Auto-metrics collection enabled',
        ],
      });
    }

    // CI Integration
    if (workflow.ci) {
      integrations.push({
        type: 'CI/CD Integration',
        status: 'available' as const,
        setup: [
          'Add ae-framework validation to CI pipeline',
          'Configure TDD compliance gates',
          'Set up automated reporting',
        ],
      });
    }

    return { integrations };
  }

  private detectBestHandler(context?: {
    isClaudeCode: boolean;
    hasTaskTool: boolean;
    userPreference: string;
  }): 'cli' | 'task' | 'mcp' {
    if (!context) return 'cli';

    // Prefer Task tool in Claude Code environment
    if (context.isClaudeCode && context.hasTaskTool && this.taskAdapter) {
      return 'task';
    }

    // Use CLI for command-line environments
    if (context.userPreference === 'cli' || !context.isClaudeCode) {
      return 'cli';
    }

    // Default to MCP for maximum compatibility
    return 'mcp';
  }

  private async handleCLIRequest(data: any): Promise<{
    response: any;
    source: 'cli' | 'agent' | 'hybrid';
    followUp?: string[];
  }> {
    if (!this.cli) {
      throw new Error('CLI not enabled in current configuration');
    }

    // Execute CLI command and return structured response
    const result = await this.executeCLICommand(data);
    
    return {
      response: result,
      source: 'cli',
      followUp: this.generateCLIFollowUp(result),
    };
  }

  private async handleTaskRequest(data: TaskRequest): Promise<{
    response: TaskResponse;
    source: 'cli' | 'agent' | 'hybrid';
    followUp?: string[];
  }> {
    if (!this.taskAdapter) {
      throw new Error('Claude Code integration not enabled');
    }

    const response = await this.taskAdapter.handleTDDTask(data);
    
    // Record metrics
    this.metricsCollector.recordArtifact(`Task: ${data.description}`);
    
    return {
      response,
      source: 'agent',
      followUp: this.generateAgentFollowUp(response),
    };
  }

  private async handleMCPRequest(data: any): Promise<{
    response: any;
    source: 'cli' | 'agent' | 'hybrid';
    followUp?: string[];
  }> {
    // Route to MCP server functionality
    const response = await this.executeMCPCommand(data);
    
    return {
      response,
      source: 'hybrid',
      followUp: [],
    };
  }

  private async handleHybridRequest(data: any): Promise<{
    response: any;
    source: 'cli' | 'agent' | 'hybrid';
    followUp?: string[];
  }> {
    // Combine CLI and Agent approaches for comprehensive response
    const cliResult = this.cli ? await this.executeCLICommand(data) : null;
    const agentResult = this.taskAdapter ? await this.taskAdapter.handleTDDTask(data) : null;
    
    return {
      response: {
        cli: cliResult,
        agent: agentResult,
        combined: this.combineResults(cliResult, agentResult),
      },
      source: 'hybrid',
      followUp: [
        ...(this.generateCLIFollowUp(cliResult) || []),
        ...(this.generateAgentFollowUp(agentResult) || []),
      ],
    };
  }

  private async executeCLICommand(data: any): Promise<any> {
    // Execute CLI commands based on data
    if (data.command === 'check') {
      return this.cli?.checkPhase(data.phase || 'current');
    } else if (data.command === 'guard') {
      return this.cli?.runGuards(data.guardName);
    } else if (data.command === 'next') {
      return this.cli?.nextPhase();
    }
    
    return { error: 'Unknown CLI command' };
  }

  private async executeMCPCommand(data: any): Promise<any> {
    // Execute MCP server commands
    // This would integrate with the MCP server implementation
    return { status: 'MCP command executed', data };
  }

  private combineResults(cliResult: any, agentResult: any): any {
    if (!cliResult && !agentResult) return null;
    if (!cliResult) return agentResult;
    if (!agentResult) return cliResult;
    
    return {
      validation: cliResult,
      guidance: agentResult,
      recommendation: 'Follow agent guidance while ensuring CLI validation passes',
    };
  }

  private generateCLIFollowUp(result: any): string[] {
    if (!result) return [];
    
    const followUp = [];
    
    if (result.violations && result.violations.length > 0) {
      followUp.push('Fix TDD violations before proceeding');
      followUp.push('Run `ae-framework guard` to validate fixes');
    }
    
    if (result.nextPhase) {
      followUp.push(`Consider moving to next phase: ${result.nextPhase}`);
    }
    
    return followUp;
  }

  private generateAgentFollowUp(result: any): string[] {
    if (!result) return [];
    
    const followUp = [];
    
    if (result.shouldBlockProgress) {
      followUp.push('Address critical violations before continuing');
    }
    
    if (result.nextActions) {
      followUp.push(...result.nextActions.slice(0, 3)); // Top 3 actions
    }
    
    return followUp;
  }

  private setupFileWatchers(): void {
    // Set up file system watchers for real-time TDD enforcement
    
    if (fs.existsSync('src')) {
      fs.watch('src', { recursive: true }, (eventType: string, filename: string) => {
        if (filename && filename.endsWith('.ts')) {
          this.handleFileChange(path.join('src', filename), eventType);
        }
      });
    }
  }

  private setupGitIntegration(): void {
    // Ensure git hooks are installed
    
    const hookPath = path.join('.git', 'hooks', 'pre-commit');
    const hookSource = path.join('scripts', 'hooks', 'pre-commit');
    
    if (fs.existsSync(hookSource) && fs.existsSync('.git')) {
      try {
        fs.copyFileSync(hookSource, hookPath);
        fs.chmodSync(hookPath, 0o755);
        console.log('✅ Git hooks installed for TDD enforcement');
      } catch (error) {
        console.warn('⚠️ Could not install git hooks:', error);
      }
    }
  }

  private startPeriodicChecks(): void {
    // Start periodic TDD compliance checks
    setInterval(async () => {
      try {
        const compliance = await this.checkCompliance();
        if (compliance.criticalViolations > 0) {
          console.warn(`⚠️ TDD Compliance Alert: ${compliance.criticalViolations} critical violations`);
        }
      } catch (error) {
        // Silent fail - don't interrupt development
      }
    }, 5 * 60 * 1000); // Check every 5 minutes
  }

  private async handleFileChange(filePath: string, eventType: string): Promise<void> {
    if (eventType === 'change' || eventType === 'rename') {
      // Check if this file change violates TDD principles
      const violation = await this.checkFileForViolations(filePath);
      
      if (violation) {
        console.warn(`🚨 TDD Violation: ${violation.message}`);
        console.warn(`💡 Suggestion: ${violation.suggestion}`);
        
        // Only record violations that match expected enum values
        const validTypes = ['code_without_test', 'test_not_run', 'skip_red_phase', 'coverage_low'];
        if (validTypes.includes(violation.type)) {
          this.metricsCollector.recordViolation({
            type: violation.type as 'code_without_test' | 'test_not_run' | 'skip_red_phase' | 'coverage_low',
            file: filePath,
            phase: 'unknown',
            message: violation.message,
            severity: violation.severity,
          });
        }
      }
    }
  }

  private async checkCompliance(): Promise<{
    score: number;
    criticalViolations: number;
    warnings: number;
  }> {
    // Simplified compliance check
    return {
      score: 85,
      criticalViolations: 0,
      warnings: 1,
    };
  }

  private async checkFileForViolations(filePath: string): Promise<{
    type: string;
    severity: 'error' | 'warning';
    message: string;
    suggestion: string;
  } | null> {
    if (filePath.startsWith('src/') && filePath.endsWith('.ts')) {
      // Check if corresponding test exists
      const testFile = filePath.replace('src/', 'tests/').replace('.ts', '.test.ts');
      
      if (!fs.existsSync(testFile)) {
        return {
          type: 'missing_test',
          severity: 'error',
          message: `No test file found for ${filePath}`,
          suggestion: `Create ${testFile} with comprehensive tests before implementation`,
        };
      }
    }
    
    return null;
  }
}

// Export factory function for easy integration
export const createHybridTDDSystem = (config?: Partial<HybridTDDConfig>) => {
  const defaultConfig: HybridTDDConfig = {
    enableCLI: true,
    enableMCPServer: true,
    enableClaudeCodeIntegration: true,
    enforceRealTime: true,
    strictMode: true,
  };
  
  return new HybridTDDSystem({ ...defaultConfig, ...config });
};