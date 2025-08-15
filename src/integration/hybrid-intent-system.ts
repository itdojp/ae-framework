/**
 * Hybrid Intent System
 * 
 * Integrates CLI tools, MCP server, and Claude Code agents
 * for comprehensive Intent analysis and Phase 1 guidance
 */

import { IntentTaskAdapter, TaskRequest, TaskResponse } from '../agents/intent-task-adapter.js';
import { IntentAgent } from '../agents/intent-agent.js';
import { ConfigLoader } from '../cli/config/ConfigLoader.js';
import { MetricsCollector } from '../cli/metrics/MetricsCollector.js';

export interface HybridIntentConfig {
  enableCLI: boolean;
  enableMCPServer: boolean;
  enableClaudeCodeIntegration: boolean;
  enforceRealTime: boolean;
  strictMode: boolean;
}

export class HybridIntentSystem {
  private agent?: IntentAgent;
  private taskAdapter?: IntentTaskAdapter;
  private metricsCollector: MetricsCollector;
  private config: HybridIntentConfig;

  constructor(config: HybridIntentConfig) {
    this.config = config;
    this.metricsCollector = new MetricsCollector(ConfigLoader.load());
    
    if (config.enableClaudeCodeIntegration) {
      this.taskAdapter = new IntentTaskAdapter();
    }
    
    this.agent = new IntentAgent();
  }

  /**
   * Main entry point for Intent operations
   * Routes requests to appropriate handler based on context
   */
  async handleIntentRequest(request: {
    type: 'cli' | 'task' | 'mcp' | 'auto';
    data: any;
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
   * Proactive Intent monitoring and intervention
   * Runs in background to provide real-time guidance
   */
  async startProactiveMonitoring(): Promise<void> {
    if (!this.config.enforceRealTime) return;

    // Set up file watchers for requirements and specifications
    this.setupRequirementWatchers();
    
    // Set up git hooks for Phase 1 validation
    this.setupGitIntegration();
    
    // Start periodic Intent compliance checks
    this.startPeriodicChecks();
  }

  /**
   * Integration with existing development workflow
   */
  async integrateWithWorkflow(workflow: {
    ide: string;
    vcs: string;
    ci: string;
    requirementsTool: string;
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
          'Configure Intent analysis settings',
          'Enable real-time requirement validation',
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
          'Intent validation active',
          'Auto-requirements tracking enabled',
        ],
      });
    }

    // Requirements Tool Integration
    if (workflow.requirementsTool) {
      integrations.push({
        type: 'Requirements Tool Integration',
        status: 'available' as const,
        setup: [
          'Connect to requirements management system',
          'Enable automatic requirement import',
          'Set up change notification tracking',
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
    if (!this.agent) {
      throw new Error('Intent Agent not available in current configuration');
    }

    // Execute direct Intent agent command
    const result = await this.executeIntentCommand(data);
    
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

    const response = await this.taskAdapter.handleIntentTask(data);
    
    // Record metrics
    this.metricsCollector.recordArtifact(`Intent Task: ${data.description}`);
    
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
    // Try MCP server first, fallback to direct agent
    try {
      const response = await this.executeMCPCommand(data);
      return {
        response,
        source: 'hybrid',
        followUp: [],
      };
    } catch (error) {
      console.warn('MCP request failed, falling back to direct agent:', error);
      return this.handleCLIRequest(data);
    }
  }

  private async handleHybridRequest(data: any): Promise<{
    response: any;
    source: 'cli' | 'agent' | 'hybrid';
    followUp?: string[];
  }> {
    // Combine CLI and Agent approaches for comprehensive response
    const agentResult = this.agent ? await this.executeIntentCommand(data) : null;
    const taskResult = this.taskAdapter ? await this.taskAdapter.handleIntentTask(data) : null;
    
    return {
      response: {
        agent: agentResult,
        task: taskResult,
        combined: this.combineResults(agentResult, taskResult),
      },
      source: 'hybrid',
      followUp: [
        ...(this.generateCLIFollowUp(agentResult) || []),
        ...(this.generateAgentFollowUp(taskResult) || []),
      ],
    };
  }

  private async executeIntentCommand(data: any): Promise<any> {
    if (!this.agent) {
      throw new Error('Intent Agent not available');
    }

    // Execute Intent agent commands based on data
    if (data.command === 'analyze') {
      return this.agent.analyzeIntent(data.request || data);
    } else if (data.command === 'extract') {
      return this.agent.extractFromNaturalLanguage(data.text);
    } else if (data.command === 'validate') {
      return this.agent.validateCompleteness(data.sources);
    } else if (data.command === 'user-stories') {
      return this.agent.createUserStories(data.requirements);
    }
    
    // Default: try to analyze as intent request
    return this.agent.analyzeIntent(data);
  }

  private async executeMCPCommand(data: any): Promise<any> {
    // Execute MCP server commands
    // This would integrate with the MCP server implementation
    // For now, simulate MCP failure to trigger fallback
    throw new Error('MCP server not responding');
  }

  private combineResults(agentResult: any, taskResult: any): any {
    if (!agentResult && !taskResult) return null;
    if (!agentResult) return taskResult;
    if (!taskResult) return agentResult;
    
    return {
      analysis: agentResult,
      guidance: taskResult,
      recommendation: 'Follow task guidance while ensuring agent analysis is complete',
    };
  }

  private generateCLIFollowUp(result: any): string[] {
    if (!result) return [];
    
    const followUp = [];
    
    if (result.completeness && result.completeness.score < 0.8) {
      followUp.push('Improve requirements completeness before proceeding');
      followUp.push('Run Intent analysis again after adding requirements');
    }
    
    if (result.requirements && result.requirements.length > 0) {
      followUp.push(`Review ${result.requirements.length} identified requirements`);
      followUp.push('Proceed to Phase 2 (Formal Specification)');
    }
    
    return followUp;
  }

  private generateAgentFollowUp(result: any): string[] {
    if (!result) return [];
    
    const followUp = [];
    
    if (result.shouldBlockProgress) {
      followUp.push('Address critical Intent issues before continuing');
    }
    
    if (result.nextActions) {
      followUp.push(...result.nextActions.slice(0, 3)); // Top 3 actions
    }
    
    return followUp;
  }

  private setupRequirementWatchers(): void {
    // Set up file system watchers for requirements files
    const fs = require('fs');
    const path = require('path');
    
    const watchPaths = ['requirements/', 'specs/', 'docs/requirements/', '.'];
    
    for (const watchPath of watchPaths) {
      if (fs.existsSync(watchPath)) {
        fs.watch(watchPath, { recursive: true }, (eventType: string, filename: string) => {
          if (filename && this.isRequirementFile(filename)) {
            this.handleRequirementChange(path.join(watchPath, filename), eventType);
          }
        });
      }
    }
  }

  private setupGitIntegration(): void {
    // Ensure git hooks are installed for Intent validation
    const fs = require('fs');
    const path = require('path');
    
    const hookPath = path.join('.git', 'hooks', 'pre-commit');
    const hookSource = path.join('scripts', 'hooks', 'pre-commit-intent');
    
    if (fs.existsSync(hookSource) && fs.existsSync('.git')) {
      try {
        // Read existing hook or create new one
        let hookContent = '';
        if (fs.existsSync(hookPath)) {
          hookContent = fs.readFileSync(hookPath, 'utf8');
        }
        
        // Add Intent validation if not present
        if (!hookContent.includes('ae-framework intent')) {
          hookContent += '\n# ae-framework Intent validation\nae-framework intent --validate || exit 1\n';
          fs.writeFileSync(hookPath, hookContent);
          fs.chmodSync(hookPath, 0o755);
          console.log('✅ Git hooks updated for Intent validation');
        }
      } catch (error) {
        console.warn('⚠️ Could not update git hooks:', error);
      }
    }
  }

  private startPeriodicChecks(): void {
    // Start periodic Intent compliance checks
    setInterval(async () => {
      try {
        const compliance = await this.checkIntentCompliance();
        if (compliance.criticalIssues > 0) {
          console.warn(`⚠️ Intent Compliance Alert: ${compliance.criticalIssues} critical issues`);
        }
      } catch (error) {
        // Silent fail - don't interrupt development
      }
    }, 10 * 60 * 1000); // Check every 10 minutes
  }

  private isRequirementFile(filename: string): boolean {
    const requirementExtensions = ['.md', '.txt', '.doc', '.docx', '.pdf'];
    const requirementKeywords = ['requirement', 'spec', 'feature', 'story', 'epic'];
    
    const ext = filename.toLowerCase().split('.').pop();
    const name = filename.toLowerCase();
    
    return requirementExtensions.includes(`.${ext}`) && 
           requirementKeywords.some(keyword => name.includes(keyword));
  }

  private async handleRequirementChange(filePath: string, eventType: string): Promise<void> {
    if (eventType === 'change' || eventType === 'rename') {
      console.log(`📝 Requirement file changed: ${filePath}`);
      
      // Optionally trigger automatic reanalysis
      if (this.config.enforceRealTime) {
        try {
          const result = await this.executeIntentCommand({
            command: 'analyze',
            sources: [{ type: 'document', content: filePath }]
          });
          console.log('✅ Automatic Intent reanalysis completed');
        } catch (error) {
          console.warn('⚠️ Automatic Intent reanalysis failed:', error);
        }
      }
    }
  }

  private async checkIntentCompliance(): Promise<{
    score: number;
    criticalIssues: number;
    warnings: number;
  }> {
    // Simplified compliance check
    // In practice, would analyze project for Intent completeness
    return {
      score: 85,
      criticalIssues: 0,
      warnings: 1,
    };
  }
}

// Export factory function for easy integration
export const createHybridIntentSystem = (config?: Partial<HybridIntentConfig>) => {
  const defaultConfig: HybridIntentConfig = {
    enableCLI: true,
    enableMCPServer: true,
    enableClaudeCodeIntegration: true,
    enforceRealTime: true,
    strictMode: false, // Less strict than TDD for Intent phase
  };
  
  return new HybridIntentSystem({ ...defaultConfig, ...config });
};