/**
 * Rust Verification MCP Plugin
 * Phase 2 of Issue #33: Enhanced Rust formal verification integration
 */

import { RustVerificationAgent, type RustVerificationRequest, type RustVerificationResult, type VerificationTool } from '../../agents/rust-verification-agent.js';
import { VerifyAgent } from '../../agents/verify-agent.js';
import { existsSync, realpathSync } from 'fs';
import * as path from 'path';
import {
  resolveWorkspacePath,
  toWorkspaceRelativePath,
  WorkspacePathPolicyError,
} from '../../utils/workspace-path-policy.js';
import type { 
  MCPPlugin, 
  MCPServer, 
  MCPEndpoint, 
  MCPRequest, 
  MCPResponse 
} from '../mcp-server.js';

class RustVerificationSecurityError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'RustVerificationSecurityError';
  }
}

export interface RustVerificationPluginConfig {
  enabledTools: string[];
  defaultOptions: {
    timeout: number;
    memoryLimit: number;
    unwindLimit: number;
    strictMode: boolean;
    generateReport: boolean;
  };
  projectDiscovery: {
    autoDetect: boolean;
    searchDepth: number;
  };
  security: {
    requireOperatorApproval: boolean;
    workspaceRoot?: string;
  };
}

export class RustVerificationPlugin implements MCPPlugin {
  name = 'rust-verification';
  version = '1.0.0';
  description = 'Enhanced Rust formal verification capabilities using Prusti, Kani, CBMC, Miri, and Loom';
  
  private rustAgent: RustVerificationAgent;
  private verifyAgent: VerifyAgent;
  private config: RustVerificationPluginConfig;

  constructor(config: Partial<RustVerificationPluginConfig> = {}) {
    const defaults: RustVerificationPluginConfig = {
      enabledTools: ['prusti', 'kani', 'miri'],
      defaultOptions: {
        timeout: 300,
        memoryLimit: 2048,
        unwindLimit: 10,
        strictMode: true,
        generateReport: true
      },
      projectDiscovery: {
        autoDetect: true,
        searchDepth: 5
      },
      security: {
        requireOperatorApproval: true,
      },
    };
    this.config = {
      ...defaults,
      ...config,
      defaultOptions: {
        ...defaults.defaultOptions,
        ...config.defaultOptions,
      },
      projectDiscovery: {
        ...defaults.projectDiscovery,
        ...config.projectDiscovery,
      },
      security: {
        ...defaults.security,
        ...config.security,
      },
    };

    this.rustAgent = new RustVerificationAgent();
    this.verifyAgent = new VerifyAgent();
  }

  async initialize(server: MCPServer): Promise<void> {
    console.log('🦀 Initializing Rust Verification Plugin...');

    // Check available tools
    const availableTools = this.rustAgent.getAvailableTools();
    console.log(`Available Rust verification tools: ${availableTools.join(', ')}`);

    server.on('plugin-registered', (event) => {
      if (event.plugin === this.name) {
        console.log('✅ Rust Verification Plugin registered successfully');
      }
    });

    console.log('🔧 Rust Verification Plugin initialized');
  }

  async terminate(server: MCPServer): Promise<void> {
    console.log('🛑 Terminating Rust Verification Plugin...');
    // Cleanup resources if needed
    console.log('✅ Rust Verification Plugin terminated');
  }

  get endpoints(): MCPEndpoint[] {
    return [
      {
        path: '/rust/verify',
        method: 'POST',
        handler: this.verifyRustProject.bind(this),
        description: 'Run comprehensive Rust formal verification on a project',
        authentication: true,
        parameters: [
          {
            name: 'projectPath',
            type: 'string',
            required: true,
            description: 'Path to the Rust project root (containing Cargo.toml)',
            validation: [
              {
                type: 'min',
                value: 1,
                message: 'Project path cannot be empty'
              }
            ]
          },
          {
            name: 'verificationTools',
            type: 'array',
            required: false,
            description: 'List of verification tools to use (prusti, kani, cbmc, miri, loom)',
            validation: [
              {
                type: 'enum',
                value: ['prusti', 'kani', 'cbmc', 'miri', 'loom']
              }
            ]
          },
          {
            name: 'options',
            type: 'object',
            required: false,
            description: 'Verification options and settings'
          },
          {
            name: 'sourceFiles',
            type: 'array',
            required: false,
            description: 'Specific source files to analyze (optional)'
          }
        ],
        response: {
          type: 'object',
          properties: {
            success: { name: 'success', type: 'boolean', required: true, description: 'Overall verification success' },
            results: { name: 'results', type: 'array', required: true, description: 'Detailed results from each tool' },
            summary: { name: 'summary', type: 'object', required: true, description: 'Verification summary' },
            recommendations: { name: 'recommendations', type: 'array', required: false, description: 'Improvement recommendations' }
          }
        }
      },
      {
        path: '/rust/tools',
        method: 'GET',
        handler: this.getAvailableTools.bind(this),
        description: 'Get list of available Rust verification tools',
        response: {
          type: 'object',
          properties: {
            tools: { name: 'tools', type: 'array', required: true, description: 'Available verification tools' },
            installed: { name: 'installed', type: 'array', required: true, description: 'Currently installed tools' }
          }
        }
      },
      {
        path: '/rust/projects',
        method: 'GET',
        handler: this.discoverRustProjects.bind(this),
        description: 'Discover Rust projects in the workspace',
        parameters: [
          {
            name: 'searchPath',
            type: 'string',
            required: false,
            description: 'Base path to search for Rust projects'
          },
          {
            name: 'maxDepth',
            type: 'number',
            required: false,
            description: 'Maximum search depth'
          }
        ],
        response: {
          type: 'object',
          properties: {
            projects: { name: 'projects', type: 'array', required: true, description: 'Discovered Rust projects' }
          }
        }
      },
      {
        path: '/rust/analyze',
        method: 'POST',
        handler: this.analyzeRustCode.bind(this),
        description: 'Analyze Rust code for verification readiness',
        parameters: [
          {
            name: 'projectPath',
            type: 'string',
            required: true,
            description: 'Path to the Rust project'
          },
          {
            name: 'analysisType',
            type: 'string',
            required: false,
            description: 'Type of analysis to perform'
          }
        ],
        response: {
          type: 'object',
          properties: {
            analysis: { name: 'analysis', type: 'object', required: true, description: 'Code analysis results' },
            recommendations: { name: 'recommendations', type: 'array', required: true, description: 'Analysis recommendations' }
          }
        }
      }
    ];
  }

  // Endpoint handlers
  private async verifyRustProject(request: MCPRequest): Promise<MCPResponse> {
    try {
      const body = request.body && typeof request.body === 'object'
        ? request.body as Record<string, unknown>
        : {};
      const { projectPath, verificationTools, options, sourceFiles } = body;
      const authorizationError = this.validateVerificationAuthorization(request);
      if (authorizationError) {
        return authorizationError;
      }
      const workspaceRoot = this.getWorkspaceRoot(request);
      const normalizedProjectPath = this.resolveWorkspaceRelativePath(projectPath, workspaceRoot, 'projectPath', {
        mustExist: true,
      });

      // Use default tools if not specified
      const toolsToUse = Array.isArray(verificationTools) ? verificationTools : this.config.enabledTools;
      
      // Merge with default options
      const verificationOptions = {
        ...this.config.defaultOptions,
        ...(options && typeof options === 'object' ? options : {})
      };

      // Discover source files if not provided
      let rustSourceFiles = sourceFiles;
      if (!rustSourceFiles) {
        rustSourceFiles = await this.discoverSourceFiles(normalizedProjectPath.absolutePath);
      }
      const normalizedSourceFiles = this.normalizeSourceFiles(rustSourceFiles, normalizedProjectPath.absolutePath);

      // Prepare verification request
      const verificationRequest: RustVerificationRequest = {
        projectPath: normalizedProjectPath.absolutePath,
        sourceFiles: normalizedSourceFiles.map((file: any) => ({
          path: file.absolutePath,
          content: file.content || '',
          annotations: file.annotations || []
        })),
        verificationTools: toolsToUse.filter((tool: any): tool is VerificationTool => 
          ['prusti', 'kani', 'cbmc', 'miri', 'loom'].includes(tool)
        ),
        options: verificationOptions
      };

      // Run verification
      const results = await this.rustAgent.verifyRustProject(verificationRequest);

      // Generate summary
      const summary = this.generateVerificationSummary(results);
      const recommendations = this.generateRecommendations(results);

      return {
        status: 200,
        data: {
          success: results.every(r => r.success),
          results,
          summary,
          recommendations,
          metadata: {
            requestId: request.context.requestId,
            timestamp: Date.now(),
            toolsUsed: toolsToUse,
            projectPath: normalizedProjectPath.relativePath
          }
        }
      };

    } catch (error) {
      if (error instanceof RustVerificationSecurityError) {
        return {
          status: 400,
          error: error.message
        };
      }
      return {
        status: 500,
        error: `Rust verification failed: ${error instanceof Error ? error.message : 'Unknown error'}`
      };
    }
  }

  private async getAvailableTools(request: MCPRequest): Promise<MCPResponse> {
    try {
      const allTools = ['prusti', 'kani', 'cbmc', 'miri', 'loom'];
      const installedTools: VerificationTool[] = this.rustAgent.getAvailableTools();

      return {
        status: 200,
        data: {
          tools: allTools.map(tool => ({
            name: tool,
            installed: installedTools.includes(tool as VerificationTool),
            description: this.getToolDescription(tool as VerificationTool)
          })),
          installed: installedTools,
          metadata: {
            timestamp: Date.now(),
            totalTools: allTools.length,
            installedCount: installedTools.length
          }
        }
      };

    } catch (error) {
      return {
        status: 500,
        error: `Failed to get available tools: ${error instanceof Error ? error.message : 'Unknown error'}`
      };
    }
  }

  private async discoverRustProjects(request: MCPRequest): Promise<MCPResponse> {
    try {
      const workspaceRoot = this.getWorkspaceRoot(request);
      const searchPathParam = (request.params as any)['searchPath'] || '.';
      const searchPath = this.resolveWorkspaceRelativePath(searchPathParam, workspaceRoot, 'searchPath', {
        mustExist: true,
      });
      const maxDepth = (request.params as any)['maxDepth'] || this.config.projectDiscovery.searchDepth;

      const projects = await this.findRustProjects(searchPath.absolutePath, maxDepth);

      return {
        status: 200,
        data: {
          projects: projects.map(project => ({
            path: project.path,
            name: project.name,
            hasTests: project.hasTests,
            dependencies: project.dependencies,
            metadata: project.metadata
          })),
          metadata: {
            searchPath: searchPath.relativePath,
            maxDepth,
            projectsFound: projects.length,
            timestamp: Date.now()
          }
        }
      };

    } catch (error) {
      if (error instanceof RustVerificationSecurityError) {
        return {
          status: 400,
          error: error.message
        };
      }
      return {
        status: 500,
        error: `Failed to discover Rust projects: ${error instanceof Error ? error.message : 'Unknown error'}`
      };
    }
  }

  private async analyzeRustCode(request: MCPRequest): Promise<MCPResponse> {
    try {
      const body = request.body && typeof request.body === 'object'
        ? request.body as Record<string, unknown>
        : {};
      const { projectPath } = body;
      const analysisType = typeof body['analysisType'] === 'string' ? body['analysisType'] : 'verification-readiness';
      const workspaceRoot = this.getWorkspaceRoot(request);
      const normalizedProjectPath = this.resolveWorkspaceRelativePath(projectPath, workspaceRoot, 'projectPath', {
        mustExist: true,
      });

      const analysis = await this.performCodeAnalysis(normalizedProjectPath.absolutePath, analysisType);
      const recommendations = this.generateAnalysisRecommendations(analysis);

      return {
        status: 200,
        data: {
          analysis,
          recommendations,
          metadata: {
            projectPath: normalizedProjectPath.relativePath,
            analysisType,
            timestamp: Date.now()
          }
        }
      };

    } catch (error) {
      if (error instanceof RustVerificationSecurityError) {
        return {
          status: 400,
          error: error.message
        };
      }
      return {
        status: 500,
        error: `Code analysis failed: ${error instanceof Error ? error.message : 'Unknown error'}`
      };
    }
  }

  // Helper methods
  private validateVerificationAuthorization(request: MCPRequest): MCPResponse | null {
    const user = request.user;
    const permissions = new Set(user?.permissions || []);
    const roles = new Set(user?.roles || []);
    const authorized = permissions.has('rust:verify')
      || roles.has('admin')
      || roles.has('operator');
    if (!authorized) {
      return {
        status: 403,
        error: 'Rust verification requires rust:verify permission or admin/operator role'
      };
    }

    if (!this.config.security.requireOperatorApproval) {
      return null;
    }

    const body = request.body && typeof request.body === 'object'
      ? request.body as Record<string, unknown>
      : {};
    const options = body['options'] && typeof body['options'] === 'object'
      ? body['options'] as Record<string, unknown>
      : {};
    const approvalCandidate = body['approval'] && typeof body['approval'] === 'object'
      ? body['approval']
      : options['approval'];
    const approval = approvalCandidate && typeof approvalCandidate === 'object'
      ? approvalCandidate as Record<string, unknown>
      : {};
    const approved = approval['approved'] === true && approval['scope'] === 'rust-verification';
    if (!approved) {
      return {
        status: 403,
        error: 'Rust verification requires explicit operator approval with approval.scope=rust-verification'
      };
    }
    return null;
  }

  private getWorkspaceRoot(request: MCPRequest): string {
    const configuredRoot = this.config.security.workspaceRoot || request.context.projectRoot;
    const absoluteRoot = path.resolve(configuredRoot);
    return existsSync(absoluteRoot) ? this.safeRealpath(absoluteRoot, 'workspaceRoot') : absoluteRoot;
  }

  private hasUnsafeRelativePath(value: string): boolean {
    return value.split(/[\\/]+/u).some((segment) => segment === '..' || segment.toLowerCase() === '.git');
  }

  private safeRealpath(value: string, label: string): string {
    try {
      return realpathSync(value);
    } catch {
      throw new RustVerificationSecurityError(`${label} could not be resolved safely`);
    }
  }

  private resolveWorkspaceRelativePath(
    value: unknown,
    root: string,
    label: string,
    { mustExist = false }: { mustExist?: boolean } = {},
  ): { absolutePath: string; relativePath: string } {
    if (typeof value !== 'string' || value.trim().length === 0) {
      throw new RustVerificationSecurityError(`${label} must be a non-empty repository-relative path`);
    }
    const rawPath = value.trim();
    if (/[\u0000-\u001f\u007f]/u.test(rawPath)) {
      throw new RustVerificationSecurityError(`${label} must not contain control characters`);
    }
    if (path.isAbsolute(rawPath) || path.win32.isAbsolute(rawPath)) {
      throw new RustVerificationSecurityError(`${label} must be repository-relative`);
    }
    if (this.hasUnsafeRelativePath(rawPath)) {
      throw new RustVerificationSecurityError(`${label} must not contain parent-directory or .git segments`);
    }

    let absolutePath: string;
    try {
      absolutePath = rawPath === '.'
        ? root
        : resolveWorkspacePath(rawPath, { workspaceRoot: root, label });
    } catch (error) {
      if (error instanceof WorkspacePathPolicyError) {
        throw new RustVerificationSecurityError(error.message);
      }
      throw error;
    }
    if (mustExist && !existsSync(absolutePath)) {
      throw new RustVerificationSecurityError(`${label} does not exist inside the configured workspace root`);
    }

    const realPath = existsSync(absolutePath) ? this.safeRealpath(absolutePath, label) : absolutePath;
    try {
      return {
        absolutePath: realPath,
        relativePath: toWorkspaceRelativePath(realPath, { workspaceRoot: root, label }),
      };
    } catch (error) {
      if (error instanceof WorkspacePathPolicyError) {
        throw new RustVerificationSecurityError(error.message);
      }
      throw error;
    }
  }

  private resolveProjectRelativePath(
    value: unknown,
    projectRoot: string,
    label: string,
  ): { absolutePath: string; relativePath: string } {
    return this.resolveWorkspaceRelativePath(value, projectRoot, label);
  }

  private normalizeSourceFiles(sourceFiles: unknown, projectRoot: string): Array<{ absolutePath: string; content: string; annotations: any[] }> {
    if (!Array.isArray(sourceFiles)) {
      throw new RustVerificationSecurityError('sourceFiles must be an array when provided');
    }
    return sourceFiles.map((file, index) => {
      const fileRecord = typeof file === 'object' && file !== null
        ? file as Record<string, unknown>
        : {};
      const sourcePath = typeof file === 'string' ? file : fileRecord['path'];
      const normalizedPath = this.resolveProjectRelativePath(sourcePath, projectRoot, `sourceFiles[${index}].path`);
      return {
        absolutePath: normalizedPath.absolutePath,
        content: typeof fileRecord['content'] === 'string' ? fileRecord['content'] : '',
        annotations: Array.isArray(fileRecord['annotations']) ? fileRecord['annotations'] : [],
      };
    });
  }

  private async discoverSourceFiles(projectPath: string): Promise<Array<{path: string, content: string}>> {
    const fs = await import('fs/promises');
    const path = await import('path');
    const files: Array<{path: string, content: string}> = [];

    try {
      const srcDir = path.join(projectPath, 'src');
      const dirContents = await fs.readdir(srcDir, { recursive: true });
      
      for (const file of dirContents) {
        if (typeof file === 'string' && file.endsWith('.rs')) {
          const fullPath = path.join(srcDir, file);
          try {
            const content = await fs.readFile(fullPath, 'utf-8');
              files.push({ path: path.relative(projectPath, fullPath), content });
          } catch (error) {
            console.warn(`Could not read file ${fullPath}:`, error);
          }
        }
      }
    } catch (error) {
      console.warn(`Could not discover source files in ${projectPath}:`, error);
    }

    return files;
  }

  private generateVerificationSummary(results: RustVerificationResult[]): any {
    const totalTools = results.length;
    const successfulTools = results.filter(r => r.success).length;
    const totalChecks = results.reduce((sum, r) => sum + r.results.length, 0);
    const passedChecks = results.reduce((sum, r) => sum + r.results.filter(check => check.status === 'passed').length, 0);
    const totalErrors = results.reduce((sum, r) => sum + r.errors.length, 0);
    const totalWarnings = results.reduce((sum, r) => sum + r.warnings.length, 0);

    return {
      totalTools,
      successfulTools,
      failedTools: totalTools - successfulTools,
      totalChecks,
      passedChecks,
      failedChecks: totalChecks - passedChecks,
      totalErrors,
      totalWarnings,
      overallSuccess: successfulTools === totalTools && totalErrors === 0,
      averageExecutionTime: results.reduce((sum, r) => sum + r.performance.executionTime, 0) / totalTools,
      toolResults: results.map(r => ({
        tool: r.tool,
        success: r.success,
        checksPassed: r.results.filter(check => check.status === 'passed').length,
        checksTotal: r.results.length,
        executionTime: r.performance.executionTime,
        memoryUsage: r.performance.memoryUsage
      }))
    };
  }

  private generateRecommendations(results: RustVerificationResult[]): string[] {
    const recommendations: string[] = [];

    // Check for failed verifications
    const failedTools = results.filter(r => !r.success);
    if (failedTools.length > 0) {
      recommendations.push(`${failedTools.length} verification tools failed - review error messages and fix issues`);
    }

    // Check for errors
    const totalErrors = results.reduce((sum, r) => sum + r.errors.length, 0);
    if (totalErrors > 0) {
      recommendations.push(`${totalErrors} verification errors detected - address critical issues before deployment`);
    }

    // Check for warnings
    const totalWarnings = results.reduce((sum, r) => sum + r.warnings.length, 0);
    if (totalWarnings > 0) {
      recommendations.push(`${totalWarnings} warnings found - consider addressing for better code quality`);
    }

    // Performance recommendations
    const slowTools = results.filter(r => r.performance.executionTime > 10000);
    if (slowTools.length > 0) {
      recommendations.push(`${slowTools.length} tools took longer than 10 seconds - consider optimizing verification setup`);
    }

    // Memory usage recommendations
    const memoryHungryTools = results.filter(r => r.performance.memoryUsage > 1000);
    if (memoryHungryTools.length > 0) {
      recommendations.push(`${memoryHungryTools.length} tools used significant memory - monitor resource usage`);
    }

    return recommendations.length > 0 ? recommendations : ['All verifications completed successfully - good code quality!'];
  }

  private getToolDescription(tool: VerificationTool): string {
    const descriptions = {
      'prusti': 'Rust ownership and borrowing verification using Viper intermediate language',
      'kani': 'Bounded model checking for Rust using CBMC',
      'cbmc': 'Bounded model checking for memory safety and assertions',
      'miri': 'Interpreter for detecting undefined behavior in unsafe Rust',
      'loom': 'Concurrency testing framework for Rust'
    };

    return descriptions[tool as keyof typeof descriptions] || 'Rust verification tool';
  }

  private async findRustProjects(basePath: string, maxDepth: number): Promise<Array<{
    path: string;
    name: string;
    hasTests: boolean;
    dependencies: string[];
    metadata: any;
  }>> {
    const fs = await import('fs/promises');
    const path = await import('path');
    const projects: Array<{
      path: string;
      name: string;
      hasTests: boolean;
      dependencies: string[];
      metadata: any;
    }> = [];

    async function searchDirectory(dir: string, currentDepth: number): Promise<void> {
      if (currentDepth > maxDepth) return;

      try {
        const items = await fs.readdir(dir, { withFileTypes: true });
        
        // Check if this directory has Cargo.toml (Rust project)
        const hasCargoToml = items.some(item => item.isFile() && item.name === 'Cargo.toml');
        
        if (hasCargoToml) {
          try {
            const cargoPath = path.join(dir, 'Cargo.toml');
            const hasTests = items.some(item => item.isDirectory() && item.name === 'tests');
            
            projects.push({
              path: dir,
              name: path.basename(dir),
              hasTests,
              dependencies: [],
              metadata: {
                cargoToml: cargoPath,
                hasCargoToml: true
              }
            });
          } catch (error) {
            console.warn(`Error reading Cargo.toml in ${dir}:`, error);
          }
        }

        // Continue searching subdirectories
        for (const item of items) {
          if (item.isDirectory() && !item.name.startsWith('.') && item.name !== 'target') {
            await searchDirectory(path.join(dir, item.name), currentDepth + 1);
          }
        }
      } catch (error) {
        console.warn(`Error searching directory ${dir}:`, error);
      }
    }

    await searchDirectory(basePath, 0);
    return projects;
  }

  private async performCodeAnalysis(projectPath: string, analysisType: string): Promise<any> {
    // Simplified analysis - in a real implementation, this would be more comprehensive
    const fs = await import('fs/promises');
    const path = await import('path');

    try {
      const srcDir = path.join(projectPath, 'src');
      const files = await fs.readdir(srcDir, { recursive: true });
      const rustFiles = files.filter(file => typeof file === 'string' && file.endsWith('.rs'));

      const analysis = {
        analysisType,
        projectStructure: {
          totalRustFiles: rustFiles.length,
          hasLibRs: rustFiles.includes('lib.rs'),
          hasMainRs: rustFiles.includes('main.rs'),
          testFiles: rustFiles.filter(file => file.includes('test') || file.includes('spec')).length
        },
        verificationReadiness: {
          score: 0.8, // Simplified score
          readyForVerification: true,
          suggestedTools: ['prusti', 'miri'],
          potentialIssues: []
        }
      };

      return analysis;

    } catch (error) {
      throw new Error(`Code analysis failed: ${error instanceof Error ? error.message : 'Unknown error'}`);
    }
  }

  private generateAnalysisRecommendations(analysis: any): string[] {
    const recommendations: string[] = [];

    if (analysis.projectStructure.totalRustFiles === 0) {
      recommendations.push('No Rust source files found - ensure project structure is correct');
    }

    if (analysis.projectStructure.testFiles === 0) {
      recommendations.push('No test files detected - consider adding unit tests for better verification coverage');
    }

    if (!analysis.projectStructure.hasLibRs && !analysis.projectStructure.hasMainRs) {
      recommendations.push('Neither lib.rs nor main.rs found - verify project structure');
    }

    if (analysis.verificationReadiness.score < 0.7) {
      recommendations.push('Project may not be ready for comprehensive verification - address structural issues first');
    } else {
      recommendations.push('Project appears ready for formal verification - consider running full verification suite');
    }

    return recommendations;
  }
}
