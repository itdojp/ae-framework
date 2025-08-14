/**
 * Context Manager for ae-framework
 * Manages context window and optimizes information flow to AI agents
 */

import { TokenOptimizer, CompressionOptions, TokenStats } from './token-optimizer.js';
import { SteeringLoader } from './steering-loader.js';
import { PhaseStateManager, PhaseType } from './phase-state-manager.js';
import * as fs from 'fs/promises';
import * as path from 'path';

export interface ContextWindow {
  steering: string;
  phaseInfo: string;
  workingMemory: string;
  relevantFiles: string;
  totalTokens: number;
}

export interface ContextOptions {
  maxTokens?: number;
  includeHistory?: boolean;
  includeArtifacts?: boolean;
  focusPhase?: PhaseType;
  relevantKeywords?: string[];
}

export class ContextManager {
  private tokenOptimizer: TokenOptimizer;
  private steeringLoader: SteeringLoader;
  private phaseStateManager: PhaseStateManager;
  private workingMemory: Map<string, any> = new Map();
  private readonly DEFAULT_MAX_TOKENS = 8000;
  private readonly STEERING_TOKEN_BUDGET = 2000;
  private readonly PHASE_TOKEN_BUDGET = 1500;
  private readonly TOKEN_ESTIMATE_RATIO = 0.25; // Same as TokenOptimizer for consistency
  private readonly FILES_TOKEN_BUDGET = 3500;

  constructor(projectRoot?: string) {
    const root = projectRoot || process.cwd();
    this.tokenOptimizer = new TokenOptimizer();
    this.steeringLoader = new SteeringLoader(root);
    this.phaseStateManager = new PhaseStateManager(root);
  }

  /**
   * Build optimized context for current phase
   */
  async buildContext(options: ContextOptions = {}): Promise<ContextWindow> {
    const {
      maxTokens = this.DEFAULT_MAX_TOKENS,
      includeHistory = true,
      includeArtifacts = true,
      focusPhase,
      relevantKeywords = []
    } = options;

    // Get current phase
    const state = await this.phaseStateManager.getCurrentState();
    const currentPhase = focusPhase || state?.currentPhase;

    // Allocate token budget
    const budgets = this.allocateTokenBudget(maxTokens);

    // Build context components
    const steering = await this.buildSteeringContext(budgets.steering, currentPhase);
    const phaseInfo = await this.buildPhaseContext(
      budgets.phase,
      currentPhase,
      includeHistory,
      includeArtifacts
    );
    const workingMemory = await this.buildWorkingMemory(budgets.memory);
    const relevantFiles = await this.buildRelevantFiles(
      budgets.files,
      currentPhase,
      relevantKeywords
    );

    // Calculate total tokens
    const totalTokens = 
      this.estimateTokens(steering) +
      this.estimateTokens(phaseInfo) +
      this.estimateTokens(workingMemory) +
      this.estimateTokens(relevantFiles);

    return {
      steering,
      phaseInfo,
      workingMemory,
      relevantFiles,
      totalTokens
    };
  }

  /**
   * Build steering context with compression
   */
  private async buildSteeringContext(
    tokenBudget: number,
    currentPhase?: PhaseType
  ): Promise<string> {
    const docs = await this.steeringLoader.loadAllDocuments();
    
    // Prioritize documents based on current phase
    const priority = this.getSteeringPriority(currentPhase);
    
    const { compressed } = await this.tokenOptimizer.compressSteeringDocuments(docs, {
      maxTokens: tokenBudget,
      preservePriority: priority,
      compressionLevel: 'medium'
    });

    return `# PROJECT CONTEXT\n${compressed}`;
  }

  /**
   * Build phase-specific context
   */
  private async buildPhaseContext(
    tokenBudget: number,
    currentPhase?: PhaseType,
    includeHistory: boolean = true,
    includeArtifacts: boolean = true
  ): Promise<string> {
    if (!currentPhase) return '';

    const state = await this.phaseStateManager.getCurrentState();
    if (!state) return '';

    let context = `# PHASE INFORMATION\n`;
    context += `Current Phase: ${currentPhase}\n`;
    context += `Progress: ${await this.phaseStateManager.getProgressPercentage()}%\n\n`;

    // Add phase status
    const phaseStatus = state.phaseStatus[currentPhase];
    if (phaseStatus) {
      context += `## Current Phase Status\n`;
      context += `- Started: ${phaseStatus.startedAt || 'Not started'}\n`;
      context += `- Completed: ${phaseStatus.completed ? 'Yes' : 'No'}\n`;
      context += `- Approved: ${phaseStatus.approved ? 'Yes' : 'No'}\n`;
      
      if (includeArtifacts && phaseStatus.artifacts.length > 0) {
        context += `- Artifacts: ${phaseStatus.artifacts.join(', ')}\n`;
      }
    }

    // Add phase history if requested
    if (includeHistory) {
      const timeline = await this.phaseStateManager.getPhaseTimeline();
      context += `\n## Phase Timeline\n`;
      for (const entry of timeline.slice(-5)) { // Last 5 entries
        context += `- ${entry.phase}: ${entry.status}`;
        if (entry.duration) {
          const minutes = Math.round(entry.duration / 1000 / 60);
          context += ` (${minutes} min)`;
        }
        context += '\n';
      }
    }

    // Compress if needed
    if (this.estimateTokens(context) > tokenBudget) {
      const { optimized } = await this.tokenOptimizer.optimizeContext(
        context,
        tokenBudget,
        [currentPhase]
      );
      return optimized;
    }

    return context;
  }

  /**
   * Build working memory context
   */
  private async buildWorkingMemory(tokenBudget: number): Promise<string> {
    if (this.workingMemory.size === 0) return '';

    let memory = '# WORKING MEMORY\n';
    const entries = Array.from(this.workingMemory.entries());
    
    // Sort by recency (assuming later entries are more recent)
    entries.reverse();

    for (const [key, value] of entries) {
      const entry = `\n## ${key}\n${JSON.stringify(value, null, 2)}\n`;
      
      if (this.estimateTokens(memory + entry) <= tokenBudget) {
        memory += entry;
      } else {
        break;
      }
    }

    return memory;
  }

  /**
   * Build relevant files context
   */
  private async buildRelevantFiles(
    tokenBudget: number,
    currentPhase?: PhaseType,
    keywords: string[] = []
  ): Promise<string> {
    const relevantFiles = await this.findRelevantFiles(currentPhase, keywords);
    if (relevantFiles.length === 0) return '';

    let filesContext = '# RELEVANT FILES\n';
    let usedTokens = this.estimateTokens(filesContext);

    for (const file of relevantFiles) {
      try {
        const content = await fs.readFile(file.path, 'utf-8');
        const compressed = await this.compressFileContent(content, file.type);
        
        const fileSection = `\n## ${file.name}\n\`\`\`${file.type}\n${compressed}\n\`\`\`\n`;
        const sectionTokens = this.estimateTokens(fileSection);
        
        if (usedTokens + sectionTokens <= tokenBudget) {
          filesContext += fileSection;
          usedTokens += sectionTokens;
        } else {
          // Try to fit a truncated version
          const remainingBudget = tokenBudget - usedTokens;
          if (remainingBudget > 100) {
            const truncated = this.truncateToTokens(compressed, remainingBudget - 50);
            filesContext += `\n## ${file.name} (truncated)\n\`\`\`${file.type}\n${truncated}\n...\n\`\`\`\n`;
          }
          break;
        }
      } catch (error) {
        // Skip files that can't be read
        continue;
      }
    }

    return filesContext;
  }

  /**
   * Find relevant files based on phase and keywords
   */
  private async findRelevantFiles(
    phase?: PhaseType,
    keywords: string[] = []
  ): Promise<Array<{ path: string; name: string; type: string; relevance: number }>> {
    const files: Array<{ path: string; name: string; type: string; relevance: number }> = [];

    // Phase-specific file patterns
    const phasePatterns: Record<PhaseType, string[]> = {
      intent: ['requirements', 'user-stories', 'README'],
      formal: ['spec', 'openapi', 'schema', 'swagger'],
      test: ['test', 'spec', '.test.', '.spec.'],
      code: ['src/', 'lib/', 'index'],
      verify: ['test', 'coverage', 'report'],
      operate: ['deploy', 'config', 'docker', 'k8s']
    };

    // Get patterns for current phase
    const patterns = phase ? phasePatterns[phase] : [];
    
    // Scan project directory
    const projectRoot = process.cwd();
    const allFiles = await this.scanDirectory(projectRoot);

    for (const filePath of allFiles) {
      const fileName = path.basename(filePath);
      const fileExt = path.extname(filePath).slice(1);
      
      let relevance = 0;

      // Check phase patterns
      for (const pattern of patterns) {
        if (filePath.includes(pattern) || fileName.includes(pattern)) {
          relevance += 10;
        }
      }

      // Check keywords
      for (const keyword of keywords) {
        if (fileName.toLowerCase().includes(keyword.toLowerCase())) {
          relevance += 5;
        }
      }

      if (relevance > 0) {
        files.push({
          path: filePath,
          name: path.relative(projectRoot, filePath),
          type: fileExt || 'txt',
          relevance
        });
      }
    }

    // Sort by relevance and return top files
    files.sort((a, b) => b.relevance - a.relevance);
    return files.slice(0, 10); // Top 10 files
  }

  /**
   * Scan directory for files
   */
  private async scanDirectory(dir: string, maxDepth: number = 3): Promise<string[]> {
    const files: string[] = [];
    
    if (maxDepth <= 0) return files;

    try {
      const entries = await fs.readdir(dir, { withFileTypes: true });
      
      for (const entry of entries) {
        const fullPath = path.join(dir, entry.name);
        
        // Skip node_modules, .git, etc.
        if (entry.name.startsWith('.') || entry.name === 'node_modules' || entry.name === 'dist') {
          continue;
        }
        
        if (entry.isDirectory()) {
          const subFiles = await this.scanDirectory(fullPath, maxDepth - 1);
          files.push(...subFiles);
        } else if (entry.isFile()) {
          // Only include text files
          const ext = path.extname(entry.name);
          if (['.ts', '.js', '.json', '.md', '.txt', '.yaml', '.yml'].includes(ext)) {
            files.push(fullPath);
          }
        }
      }
    } catch (error) {
      // Ignore errors (e.g., permission denied)
    }

    return files;
  }

  /**
   * Compress file content based on type
   */
  private async compressFileContent(content: string, fileType: string): Promise<string> {
    // Remove comments for code files
    if (['ts', 'js', 'tsx', 'jsx'].includes(fileType)) {
      content = content.replace(/\/\*[\s\S]*?\*\//g, ''); // Block comments
      content = content.replace(/\/\/.*/g, ''); // Line comments
    }

    // Remove empty lines
    content = content.replace(/^\s*[\r\n]/gm, '');

    // Limit line length
    const lines = content.split('\n');
    const compressed = lines.map(line => 
      line.length > 120 ? line.substring(0, 120) + '...' : line
    ).join('\n');

    return compressed;
  }

  /**
   * Get steering document priority based on phase
   */
  private getSteeringPriority(phase?: PhaseType): string[] {
    if (!phase) return ['product', 'architecture', 'standards'];

    const phasePriority: Record<PhaseType, string[]> = {
      intent: ['product', 'standards', 'architecture'],
      formal: ['architecture', 'standards', 'product'],
      test: ['standards', 'architecture', 'product'],
      code: ['standards', 'architecture', 'product'],
      verify: ['standards', 'product', 'architecture'],
      operate: ['architecture', 'standards', 'product']
    };

    return phasePriority[phase];
  }

  /**
   * Allocate token budget across context components
   */
  private allocateTokenBudget(totalTokens: number): {
    steering: number;
    phase: number;
    memory: number;
    files: number;
  } {
    const steeringRatio = 0.25;
    const phaseRatio = 0.20;
    const memoryRatio = 0.15;
    const filesRatio = 0.40;

    return {
      steering: Math.floor(totalTokens * steeringRatio),
      phase: Math.floor(totalTokens * phaseRatio),
      memory: Math.floor(totalTokens * memoryRatio),
      files: Math.floor(totalTokens * filesRatio)
    };
  }

  /**
   * Add item to working memory
   */
  addToMemory(key: string, value: any): void {
    // Limit memory size
    if (this.workingMemory.size >= 20) {
      // Remove oldest entry
      const firstKey = this.workingMemory.keys().next().value;
      if (firstKey !== undefined) {
        this.workingMemory.delete(firstKey);
      }
    }
    this.workingMemory.set(key, value);
  }

  /**
   * Clear working memory
   */
  clearMemory(): void {
    this.workingMemory.clear();
  }

  /**
   * Get memory item
   */
  getFromMemory(key: string): any {
    return this.workingMemory.get(key);
  }

  /**
   * Estimate token count - delegates to TokenOptimizer for consistency
   */
  private estimateTokens(text: string): number {
    return this.tokenOptimizer.estimateTokens(text);
  }

  /**
   * Truncate text to token limit
   */
  private truncateToTokens(text: string, maxTokens: number): string {
    const estimatedChars = Math.floor(maxTokens / this.TOKEN_ESTIMATE_RATIO);
    return text.length > estimatedChars 
      ? text.substring(0, estimatedChars)
      : text;
  }

  /**
   * Get context statistics
   */
  async getContextStats(options: ContextOptions = {}): Promise<{
    components: Record<string, number>;
    total: number;
    compressionRatio: number;
  }> {
    const context = await this.buildContext(options);
    
    const components = {
      steering: this.estimateTokens(context.steering),
      phase: this.estimateTokens(context.phaseInfo),
      memory: this.estimateTokens(context.workingMemory),
      files: this.estimateTokens(context.relevantFiles)
    };

    return {
      components,
      total: context.totalTokens,
      compressionRatio: 0.7 // Approximate compression ratio
    };
  }
}