/**
 * Base Command for Extended Commands
 * Provides common functionality and unified interface
 */

import type { CommandResult, CommandContext } from '../slash-command-manager.js';
import { EvidenceValidator } from '../../utils/evidence-validator.js';

export interface ExtendedCommandConfig {
  name: string;
  description: string;
  usage: string;
  aliases?: string[];
  category: 'utility' | 'analysis' | 'documentation';
}

export interface ExtendedCommandResult<T = any> {
  success: boolean;
  message: string;
  data?: T;
  evidence?: any[];
  metrics?: CommandMetrics;
}

export interface CommandMetrics {
  executionTime: number;
  filesProcessed: number;
  confidence?: number;
}

export abstract class BaseExtendedCommand {
  public readonly name: string;
  public readonly description: string;
  public readonly category = 'utility' as const;
  public readonly usage: string;
  public readonly aliases?: string[];

  protected validator: EvidenceValidator;
  private metrics: Map<string, number> = new Map();
  
  constructor(config?: ExtendedCommandConfig) {
    // Set default values, will be overridden by subclasses
    this.name = config?.name || '';
    this.description = config?.description || '';
    this.usage = config?.usage || '';
    this.aliases = config?.aliases || [];
    this.validator = new EvidenceValidator();
  }

  /**
   * Record metric for performance tracking
   */
  protected recordMetric(key: string, value?: number): void {
    if (value !== undefined) {
      this.metrics.set(key, value);
    } else {
      const currentValue = this.metrics.get(key) || 0;
      this.metrics.set(key, currentValue + 1);
    }
  }

  /**
   * Get recorded metrics
   */
  protected getMetrics(): Map<string, number> {
    return new Map(this.metrics);
  }

  /**
   * Main handler method - implements common flow
   */
  async handler(args: string[], context: CommandContext): Promise<CommandResult> {
    const startTime = Date.now();
    
    try {
      // Validate arguments
      const validationResult = this.validateArgs(args);
      if (!validationResult.isValid) {
        return {
          success: false,
          message: validationResult.message
        };
      }

      // Parse options
      const options = this.parseOptions(args);
      
      // Execute the specific command logic
      const result = await this.execute(args, options, context);
      
      // Add metrics
      const executionTime = Date.now() - startTime;
      if (result.metrics) {
        result.metrics.executionTime = executionTime;
      } else {
        result.metrics = { executionTime, filesProcessed: 0 };
      }

      // Validate with evidence if requested
      if (options.validate && result.data) {
        result.evidence = await this.validateWithEvidence(result.data, options);
      }

      return {
        success: result.success,
        message: result.message,
        data: result.data
      };

    } catch (error: any) {
      return {
        success: false,
        message: `Command failed: ${error.message}`
      };
    }
  }

  /**
   * Validate command arguments
   */
  protected abstract validateArgs(args: string[]): { isValid: boolean; message?: string };

  /**
   * Parse command options
   */
  protected parseOptions(args: string[]): Record<string, any> {
    const options: Record<string, any> = { validate: false };
    
    for (const arg of args) {
      if (arg === '--validate') {
        options.validate = true;
      } else if (arg.startsWith('--')) {
        const [key, value] = arg.slice(2).split('=');
        options[key] = value || true;
      }
    }
    
    return options;
  }

  /**
   * Execute the specific command logic
   */
  protected abstract execute(
    args: string[], 
    options: Record<string, any>, 
    context: CommandContext
  ): Promise<ExtendedCommandResult>;

  /**
   * Validate results with evidence
   */
  protected async validateWithEvidence(
    data: any, 
    options: Record<string, any>
  ): Promise<any[]> {
    const evidence = [];
    
    try {
      const validation = await this.validator.validateClaim(
        this.generateValidationClaim(data),
        JSON.stringify(data),
        { minConfidence: options.minConfidence || 0.7 }
      );
      evidence.push(validation);
    } catch (error) {
      // Evidence validation failed, but continue
    }
    
    return evidence;
  }

  /**
   * Generate validation claim from data
   */
  protected abstract generateValidationClaim(data: any): string;

  /**
   * Generate summary for results
   */
  protected abstract generateSummary(data: any): string;
}