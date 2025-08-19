/**
 * Data Validation Monitor
 * Phase 2.2: Runtime monitor for data validation conformance rules
 */

import { v4 as uuidv4 } from 'uuid';
import { z } from 'zod';
import {
  ConformanceMonitor,
  ConformanceRule,
  RuntimeContext,
  VerificationResult,
  ViolationDetails,
  ConformanceRuleCategory
} from '../types.js';

export class DataValidationMonitor implements ConformanceMonitor {
  readonly id = 'data-validation-monitor';
  readonly name = 'Data Validation Monitor';
  
  private rules: Map<string, ConformanceRule> = new Map();
  private schemaCache: Map<string, z.ZodSchema> = new Map();

  /**
   * Verify data against validation rules
   */
  async verify(data: any, context: RuntimeContext): Promise<VerificationResult> {
    const startTime = Date.now();
    const resultId = uuidv4();

    try {
      // Get applicable rules for data validation
      const applicableRules = Array.from(this.rules.values())
        .filter(rule => rule.enabled && rule.category === 'data_validation');

      if (applicableRules.length === 0) {
        return {
          id: resultId,
          ruleId: 'none',
          status: 'skip',
          timestamp: new Date().toISOString(),
          duration: Date.now() - startTime,
          context,
          metrics: { executionTime: Date.now() - startTime }
        };
      }

      // Execute validation rules
      let violation: ViolationDetails | undefined;
      
      for (const rule of applicableRules) {
        const validationResult = await this.validateAgainstRule(data, rule, context);
        if (validationResult.violation) {
          violation = validationResult.violation;
          break; // Stop at first violation for performance
        }
      }

      const duration = Date.now() - startTime;

      return {
        id: resultId,
        ruleId: violation?.ruleId || applicableRules[0].id,
        status: violation ? 'fail' : 'pass',
        timestamp: new Date().toISOString(),
        duration,
        context,
        violation,
        metrics: {
          executionTime: duration,
          memoryUsage: this.getMemoryUsage(),
          networkCalls: 0,
          dbQueries: 0
        }
      };

    } catch (error) {
      const duration = Date.now() - startTime;
      
      return {
        id: resultId,
        ruleId: 'error',
        status: 'error',
        timestamp: new Date().toISOString(),
        duration,
        context,
        violation: {
          ruleId: 'data-validation-error',
          ruleName: 'Data Validation Error',
          category: 'data_validation',
          severity: 'major',
          message: `Data validation failed: ${error instanceof Error ? error.message : String(error)}`,
          context,
          stackTrace: error instanceof Error ? error.stack : undefined,
          evidence: { inputData: data }
        },
        metrics: { executionTime: duration }
      };
    }
  }

  /**
   * Check if this monitor can verify a specific rule
   */
  canVerify(ruleId: string): boolean {
    const rule = this.rules.get(ruleId);
    return rule?.category === 'data_validation' && rule.enabled;
  }

  /**
   * Get all rules managed by this monitor
   */
  getRules(): ConformanceRule[] {
    return Array.from(this.rules.values()).filter(rule => rule.category === 'data_validation');
  }

  /**
   * Update a rule
   */
  async updateRule(rule: ConformanceRule): Promise<void> {
    if (rule.category !== 'data_validation') {
      throw new Error(`Invalid rule category for DataValidationMonitor: ${rule.category}`);
    }
    
    this.rules.set(rule.id, rule);
    this.schemaCache.delete(rule.id); // Invalidate cached schema
  }

  /**
   * Remove a rule
   */
  async removeRule(ruleId: string): Promise<void> {
    this.rules.delete(ruleId);
    this.schemaCache.delete(ruleId);
  }

  /**
   * Validate data against a specific rule
   */
  private async validateAgainstRule(
    data: any,
    rule: ConformanceRule,
    context: RuntimeContext
  ): Promise<{ violation?: ViolationDetails }> {
    try {
      // Parse rule condition for validation schema
      const validationSchema = this.parseValidationSchema(rule);
      
      if (validationSchema) {
        // Use Zod schema validation
        const result = validationSchema.safeParse(data);
        
        if (!result.success) {
          const violation: ViolationDetails = {
            ruleId: rule.id,
            ruleName: rule.name,
            category: rule.category,
            severity: rule.severity,
            message: `Data validation failed: ${result.error.errors[0]?.message || 'Invalid data'}`,
            actualValue: data,
            expectedValue: 'Valid data according to schema',
            context,
            evidence: {
              inputData: data,
              stateSnapshot: { errors: result.error.errors },
              logs: [`Validation failed for rule: ${rule.name}`]
            },
            remediation: {
              suggested: this.generateValidationSuggestions(result.error, rule),
              automatic: false,
              priority: this.mapSeverityToPriority(rule.severity)
            }
          };
          
          return { violation };
        }
      } else {
        // Fall back to custom validation logic
        const customValidation = await this.performCustomValidation(data, rule, context);
        if (customValidation.violation) {
          return customValidation;
        }
      }

      return {};

    } catch (error) {
      const violation: ViolationDetails = {
        ruleId: rule.id,
        ruleName: rule.name,
        category: rule.category,
        severity: 'major',
        message: `Rule validation error: ${error instanceof Error ? error.message : String(error)}`,
        actualValue: data,
        context,
        stackTrace: error instanceof Error ? error.stack : undefined,
        evidence: { inputData: data }
      };

      return { violation };
    }
  }

  /**
   * Parse validation schema from rule condition
   */
  private parseValidationSchema(rule: ConformanceRule): z.ZodSchema | null {
    // Check cache first
    const cached = this.schemaCache.get(rule.id);
    if (cached) return cached;

    try {
      // Try to parse Zod-like schema from rule condition
      const condition = rule.condition.expression;
      let schema: z.ZodSchema | null = null;

      // Common validation patterns
      if (condition.includes('required')) {
        schema = z.object({}).nonstrict();
      } else if (condition.includes('string')) {
        schema = z.string();
      } else if (condition.includes('number')) {
        schema = z.number();
      } else if (condition.includes('boolean')) {
        schema = z.boolean();
      } else if (condition.includes('array')) {
        schema = z.array(z.any());
      } else if (condition.includes('object')) {
        schema = z.object({}).nonstrict();
      } else if (condition.includes('email')) {
        schema = z.string().email();
      } else if (condition.includes('url')) {
        schema = z.string().url();
      } else if (condition.includes('uuid')) {
        schema = z.string().uuid();
      }

      // Enhanced schema parsing based on constraints
      if (schema && rule.condition.constraints) {
        schema = this.applyConstraints(schema, rule.condition.constraints);
      }

      if (schema) {
        this.schemaCache.set(rule.id, schema);
      }

      return schema;

    } catch (error) {
      console.warn(`Failed to parse validation schema for rule ${rule.id}:`, error);
      return null;
    }
  }

  /**
   * Apply constraints to Zod schema
   */
  private applyConstraints(baseSchema: z.ZodSchema, constraints: Record<string, any>): z.ZodSchema {
    let schema = baseSchema;

    try {
      // String constraints
      if (schema instanceof z.ZodString) {
        if (constraints.minLength) {
          schema = (schema as z.ZodString).min(constraints.minLength);
        }
        if (constraints.maxLength) {
          schema = (schema as z.ZodString).max(constraints.maxLength);
        }
        if (constraints.pattern) {
          schema = (schema as z.ZodString).regex(new RegExp(constraints.pattern));
        }
      }

      // Number constraints
      if (schema instanceof z.ZodNumber) {
        if (constraints.min !== undefined) {
          schema = (schema as z.ZodNumber).min(constraints.min);
        }
        if (constraints.max !== undefined) {
          schema = (schema as z.ZodNumber).max(constraints.max);
        }
        if (constraints.integer) {
          schema = (schema as z.ZodNumber).int();
        }
      }

      // Array constraints
      if (schema instanceof z.ZodArray) {
        if (constraints.minItems) {
          schema = (schema as z.ZodArray<any>).min(constraints.minItems);
        }
        if (constraints.maxItems) {
          schema = (schema as z.ZodArray<any>).max(constraints.maxItems);
        }
      }

      // Optional/nullable handling
      if (constraints.optional) {
        schema = schema.optional();
      }
      if (constraints.nullable) {
        schema = schema.nullable();
      }

    } catch (error) {
      console.warn('Failed to apply constraints to schema:', error);
    }

    return schema;
  }

  /**
   * Perform custom validation logic when schema parsing fails
   */
  private async performCustomValidation(
    data: any,
    rule: ConformanceRule,
    context: RuntimeContext
  ): Promise<{ violation?: ViolationDetails }> {
    const condition = rule.condition.expression;

    try {
      // Basic type checks
      if (condition.includes('required') && (data === null || data === undefined)) {
        return {
          violation: {
            ruleId: rule.id,
            ruleName: rule.name,
            category: rule.category,
            severity: rule.severity,
            message: 'Required field is missing or null',
            actualValue: data,
            expectedValue: 'Non-null value',
            context,
            evidence: { inputData: data }
          }
        };
      }

      if (condition.includes('string') && typeof data !== 'string') {
        return {
          violation: {
            ruleId: rule.id,
            ruleName: rule.name,
            category: rule.category,
            severity: rule.severity,
            message: `Expected string, got ${typeof data}`,
            actualValue: data,
            expectedValue: 'string',
            context,
            evidence: { inputData: data }
          }
        };
      }

      if (condition.includes('number') && typeof data !== 'number') {
        return {
          violation: {
            ruleId: rule.id,
            ruleName: rule.name,
            category: rule.category,
            severity: rule.severity,
            message: `Expected number, got ${typeof data}`,
            actualValue: data,
            expectedValue: 'number',
            context,
            evidence: { inputData: data }
          }
        };
      }

      if (condition.includes('array') && !Array.isArray(data)) {
        return {
          violation: {
            ruleId: rule.id,
            ruleName: rule.name,
            category: rule.category,
            severity: rule.severity,
            message: `Expected array, got ${typeof data}`,
            actualValue: data,
            expectedValue: 'array',
            context,
            evidence: { inputData: data }
          }
        };
      }

      // Email validation
      if (condition.includes('email') && typeof data === 'string') {
        const emailRegex = /^[^\s@]+@[^\s@]+\.[^\s@]+$/;
        if (!emailRegex.test(data)) {
          return {
            violation: {
              ruleId: rule.id,
              ruleName: rule.name,
              category: rule.category,
              severity: rule.severity,
              message: 'Invalid email format',
              actualValue: data,
              expectedValue: 'Valid email address',
              context,
              evidence: { inputData: data }
            }
          };
        }
      }

      // URL validation
      if (condition.includes('url') && typeof data === 'string') {
        try {
          new URL(data);
        } catch {
          return {
            violation: {
              ruleId: rule.id,
              ruleName: rule.name,
              category: rule.category,
              severity: rule.severity,
              message: 'Invalid URL format',
              actualValue: data,
              expectedValue: 'Valid URL',
              context,
              evidence: { inputData: data }
            }
          };
        }
      }

      // UUID validation
      if (condition.includes('uuid') && typeof data === 'string') {
        const uuidRegex = /^[0-9a-f]{8}-[0-9a-f]{4}-[1-5][0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$/i;
        if (!uuidRegex.test(data)) {
          return {
            violation: {
              ruleId: rule.id,
              ruleName: rule.name,
              category: rule.category,
              severity: rule.severity,
              message: 'Invalid UUID format',
              actualValue: data,
              expectedValue: 'Valid UUID',
              context,
              evidence: { inputData: data }
            }
          };
        }
      }

      return {};

    } catch (error) {
      return {
        violation: {
          ruleId: rule.id,
          ruleName: rule.name,
          category: rule.category,
          severity: 'major',
          message: `Custom validation error: ${error instanceof Error ? error.message : String(error)}`,
          actualValue: data,
          context,
          stackTrace: error instanceof Error ? error.stack : undefined,
          evidence: { inputData: data }
        }
      };
    }
  }

  /**
   * Generate validation suggestions based on Zod errors
   */
  private generateValidationSuggestions(error: z.ZodError, rule: ConformanceRule): string[] {
    const suggestions: string[] = [];

    for (const issue of error.errors) {
      switch (issue.code) {
        case 'invalid_type':
          suggestions.push(`Convert ${issue.received} to ${issue.expected}`);
          break;
        case 'too_small':
          if (issue.type === 'string') {
            suggestions.push(`Ensure string has at least ${issue.minimum} characters`);
          } else if (issue.type === 'number') {
            suggestions.push(`Ensure number is at least ${issue.minimum}`);
          } else if (issue.type === 'array') {
            suggestions.push(`Ensure array has at least ${issue.minimum} items`);
          }
          break;
        case 'too_big':
          if (issue.type === 'string') {
            suggestions.push(`Ensure string has at most ${issue.maximum} characters`);
          } else if (issue.type === 'number') {
            suggestions.push(`Ensure number is at most ${issue.maximum}`);
          } else if (issue.type === 'array') {
            suggestions.push(`Ensure array has at most ${issue.maximum} items`);
          }
          break;
        case 'invalid_string':
          if (issue.validation === 'email') {
            suggestions.push('Provide a valid email address');
          } else if (issue.validation === 'url') {
            suggestions.push('Provide a valid URL');
          } else if (issue.validation === 'uuid') {
            suggestions.push('Provide a valid UUID');
          }
          break;
        case 'invalid_enum_value':
          suggestions.push(`Use one of the allowed values: ${issue.options.join(', ')}`);
          break;
        default:
          suggestions.push(`Fix validation error: ${issue.message}`);
      }
    }

    if (suggestions.length === 0) {
      suggestions.push('Review and fix the data according to the validation requirements');
    }

    return suggestions;
  }

  /**
   * Map severity to priority
   */
  private mapSeverityToPriority(severity: string): 'low' | 'medium' | 'high' | 'critical' {
    switch (severity) {
      case 'critical': return 'critical';
      case 'major': return 'high';
      case 'minor': return 'medium';
      case 'info':
      case 'warning':
        return 'low';
      default: return 'medium';
    }
  }

  /**
   * Get memory usage (if available)
   */
  private getMemoryUsage(): number {
    if (typeof process !== 'undefined' && process.memoryUsage) {
      return process.memoryUsage().heapUsed;
    }
    return 0;
  }

  /**
   * Create common validation rules
   */
  static createCommonRules(): ConformanceRule[] {
    const now = new Date().toISOString();

    return [
      {
        id: uuidv4(),
        name: 'Required String Fields',
        description: 'Ensures required string fields are present and not empty',
        category: 'data_validation',
        severity: 'major',
        enabled: true,
        condition: {
          expression: 'required && string',
          variables: ['data'],
          constraints: { minLength: 1 }
        },
        actions: ['log_violation'],
        metadata: {
          createdAt: now,
          updatedAt: now,
          version: '1.0.0',
          tags: ['string', 'required']
        }
      },
      {
        id: uuidv4(),
        name: 'Email Format Validation',
        description: 'Validates email address format',
        category: 'data_validation',
        severity: 'minor',
        enabled: true,
        condition: {
          expression: 'email',
          variables: ['data'],
          constraints: {}
        },
        actions: ['log_violation'],
        metadata: {
          createdAt: now,
          updatedAt: now,
          version: '1.0.0',
          tags: ['email', 'format']
        }
      },
      {
        id: uuidv4(),
        name: 'Positive Number Validation',
        description: 'Ensures numeric values are positive',
        category: 'data_validation',
        severity: 'minor',
        enabled: true,
        condition: {
          expression: 'number',
          variables: ['data'],
          constraints: { min: 0 }
        },
        actions: ['log_violation'],
        metadata: {
          createdAt: now,
          updatedAt: now,
          version: '1.0.0',
          tags: ['number', 'positive']
        }
      }
    ];
  }
}