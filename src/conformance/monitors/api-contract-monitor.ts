/**
 * API Contract Monitor
 * Phase 2.2: Runtime monitor for API contract conformance verification
 */

import { v4 as uuidv4 } from 'uuid';
import {
  ConformanceMonitor,
  ConformanceRule,
  RuntimeContext,
  VerificationResult,
  ViolationDetails,
  ConformanceRuleCategory
} from '../types.js';

// Default empty structures for evidence objects
const DEFAULT_METRICS = {};
const DEFAULT_LOGS: string[] = [];
const DEFAULT_STATE_SNAPSHOT = {};
const DEFAULT_TRACES: any[] = [];

interface APIContractSpec {
  method: string;
  path: string;
  requestSchema?: any;
  responseSchema?: any;
  headers?: Record<string, string>;
  statusCodes?: number[];
  timeout?: number;
  rateLimit?: {
    requests: number;
    window: number; // milliseconds
  };
}

interface APICallData {
  method: string;
  url: string;
  path: string;
  headers: Record<string, string>;
  body?: any;
  response?: {
    status: number;
    headers: Record<string, string>;
    body?: any;
    time: number; // response time in ms
  };
  timestamp: string;
}

export class APIContractMonitor implements ConformanceMonitor {
  readonly id = 'api-contract-monitor';
  readonly name = 'API Contract Monitor';
  
  private rules: Map<string, ConformanceRule> = new Map();
  private contractSpecs: Map<string, APIContractSpec> = new Map();
  private rateLimitTracker: Map<string, { count: number; windowStart: number }> = new Map();

  /**
   * Verify API call against contract rules
   */
  async verify(data: any, context: RuntimeContext): Promise<VerificationResult> {
    const startTime = Date.now();
    const resultId = uuidv4();

    try {
      // Validate data format
      if (!this.isAPICallData(data)) {
        return {
          id: resultId,
          ruleId: 'invalid-data',
          status: 'skip',
          timestamp: new Date().toISOString(),
          duration: Date.now() - startTime,
          context,
          metrics: {
            networkCalls: 0, // TODO: Implement
            dbQueries: 0, // TODO: Implement
            executionTime: Date.now() - startTime
          }
        };
      }

      const apiCall = data as APICallData;
      
      // Get applicable rules for API contracts
      const applicableRules = Array.from(this.rules.values())
        .filter(rule => rule.enabled && rule.category === 'api_contract');

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

      // Find matching contract specification
      const contractSpec = this.findMatchingContract(apiCall);
      
      // Execute contract validation rules
      let violation: ViolationDetails | undefined;
      
      for (const rule of applicableRules) {
        const validationResult = await this.validateAPIContract(apiCall, rule, contractSpec, context);
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
          networkCalls: 1,
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
          ruleId: 'api-contract-error',
          ruleName: 'API Contract Error',
          category: 'api_contract',
          severity: 'major',
          message: `API contract validation failed: ${error instanceof Error ? error.message : String(error)}`,
          metrics: undefined, // TODO: Implement
          logs: undefined, // TODO: Implement
          stateSnapshot: undefined, // TODO: Implement
          traces: undefined, // TODO: Implement
          context,
          stackTrace: error instanceof Error ? error.stack : undefined,
          evidence: { 
            inputData: data,
            metrics: DEFAULT_METRICS,
            logs: DEFAULT_LOGS,
            stateSnapshot: DEFAULT_STATE_SNAPSHOT,
            traces: DEFAULT_TRACES
          }
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
    return rule?.category === 'api_contract' && rule.enabled;
  }

  /**
   * Get all rules managed by this monitor
   */
  getRules(): ConformanceRule[] {
    return Array.from(this.rules.values()).filter(rule => rule.category === 'api_contract');
  }

  /**
   * Update a rule
   */
  async updateRule(rule: ConformanceRule): Promise<void> {
    if (rule.category !== 'api_contract') {
      throw new Error(`Invalid rule category for APIContractMonitor: ${rule.category}`);
    }
    
    this.rules.set(rule.id, rule);
  }

  /**
   * Remove a rule
   */
  async removeRule(ruleId: string): Promise<void> {
    this.rules.delete(ruleId);
  }

  /**
   * Add API contract specification
   */
  addContractSpec(path: string, spec: APIContractSpec): void {
    this.contractSpecs.set(this.normalizePathPattern(path), spec);
  }

  /**
   * Remove API contract specification
   */
  removeContractSpec(path: string): void {
    this.contractSpecs.delete(this.normalizePathPattern(path));
  }

  /**
   * Validate API call against contract
   */
  private async validateAPIContract(
    apiCall: APICallData,
    rule: ConformanceRule,
    contractSpec: APIContractSpec | null,
    context: RuntimeContext
  ): Promise<{ violation?: ViolationDetails }> {
    try {
      const ruleExpression = rule.condition.expression;
      
      // Method validation
      if (ruleExpression.includes('method') && contractSpec) {
        if (apiCall.method !== contractSpec.method) {
          return {
            violation: this.createViolation(
              rule,
              `HTTP method mismatch: expected ${contractSpec.method}, got ${apiCall.method}`,
              contractSpec.method,
              apiCall.method,
              context,
              apiCall
            )
          };
        }
      }

      // Status code validation
      if (ruleExpression.includes('status') && contractSpec?.statusCodes && apiCall.response) {
        if (!contractSpec.statusCodes.includes(apiCall.response.status)) {
          return {
            violation: this.createViolation(
              rule,
              `Invalid status code: expected one of [${contractSpec.statusCodes.join(', ')}], got ${apiCall.response.status}`,
              contractSpec.statusCodes,
              apiCall.response.status,
              context,
              apiCall
            )
          };
        }
      }

      // Response time validation
      if (ruleExpression.includes('timeout') && contractSpec?.timeout && apiCall.response) {
        if (apiCall.response.time > contractSpec.timeout) {
          return {
            violation: this.createViolation(
              rule,
              `Response timeout: expected < ${contractSpec.timeout}ms, got ${apiCall.response.time}ms`,
              `< ${contractSpec.timeout}ms`,
              `${apiCall.response.time}ms`,
              context,
              apiCall
            )
          };
        }
      }

      // Required headers validation
      if (ruleExpression.includes('headers') && contractSpec?.headers) {
        const missingHeaders = this.findMissingHeaders(apiCall, contractSpec);
        if (missingHeaders.length > 0) {
          return {
            violation: this.createViolation(
              rule,
              `Missing required headers: ${missingHeaders.join(', ')}`,
              Object.keys(contractSpec.headers),
              Object.keys(apiCall.headers),
              context,
              apiCall
            )
          };
        }
      }

      // Rate limiting validation
      if (ruleExpression.includes('rate_limit') && contractSpec?.rateLimit) {
        const rateLimitViolation = this.checkRateLimit(apiCall, contractSpec, rule, context);
        if (rateLimitViolation) {
          return { violation: rateLimitViolation };
        }
      }

      // Request body schema validation
      if (ruleExpression.includes('request_schema') && contractSpec?.requestSchema && apiCall.body) {
        const schemaViolation = this.validateSchema(
          apiCall.body,
          contractSpec.requestSchema,
          'request',
          rule,
          context,
          apiCall
        );
        if (schemaViolation) {
          return { violation: schemaViolation };
        }
      }

      // Response body schema validation
      if (ruleExpression.includes('response_schema') && contractSpec?.responseSchema && apiCall.response?.body) {
        const schemaViolation = this.validateSchema(
          apiCall.response.body,
          contractSpec.responseSchema,
          'response',
          rule,
          context,
          apiCall
        );
        if (schemaViolation) {
          return { violation: schemaViolation };
        }
      }

      // Path parameter validation
      if (ruleExpression.includes('path_params') && contractSpec) {
        const pathViolation = this.validatePathParameters(apiCall, contractSpec, rule, context);
        if (pathViolation) {
          return { violation: pathViolation };
        }
      }

      return {};

    } catch (error) {
      return {
        violation: this.createViolation(
          rule,
          `Contract validation error: ${error instanceof Error ? error.message : String(error)}`,
          'Valid contract',
          'Invalid contract',
          context,
          apiCall,
          error instanceof Error ? error.stack : undefined
        )
      };
    }
  }

  /**
   * Check if data is valid API call data
   */
  private isAPICallData(data: any): data is APICallData {
    return data && 
           typeof data.method === 'string' &&
           typeof data.url === 'string' &&
           typeof data.path === 'string' &&
           typeof data.headers === 'object' &&
           typeof data.timestamp === 'string';
  }

  /**
   * Find matching contract specification
   */
  private findMatchingContract(apiCall: APICallData): APIContractSpec | null {
    for (const [pathPattern, spec] of this.contractSpecs.entries()) {
      if (this.matchesPathPattern(apiCall.path, pathPattern) && apiCall.method === spec.method) {
        return spec;
      }
    }
    return null;
  }

  /**
   * Check if path matches pattern (supports basic wildcards)
   */
  private matchesPathPattern(path: string, pattern: string): boolean {
    // Convert pattern to regex (basic implementation)
    const regexPattern = pattern
      .replace(/\*/g, '.*')
      .replace(/\{[^}]+\}/g, '[^/]+'); // Path parameters like {id}
    
    const regex = new RegExp(`^${regexPattern}$`);
    return regex.test(path);
  }

  /**
   * Normalize path pattern for consistent storage
   */
  private normalizePathPattern(path: string): string {
    return path.replace(/\/+/g, '/').replace(/\/$/, '') || '/';
  }

  /**
   * Find missing required headers
   */
  private findMissingHeaders(apiCall: APICallData, contractSpec: APIContractSpec): string[] {
    const missing: string[] = [];
    
    for (const [headerName, expectedValue] of Object.entries(contractSpec.headers || {})) {
      const actualValue = apiCall.headers[headerName] || apiCall.headers[headerName.toLowerCase()];
      
      if (!actualValue) {
        missing.push(headerName);
      } else if (expectedValue !== '*' && actualValue !== expectedValue) {
        missing.push(`${headerName}:${expectedValue}`);
      }
    }
    
    return missing;
  }

  /**
   * Check rate limiting
   */
  private checkRateLimit(
    apiCall: APICallData,
    contractSpec: APIContractSpec,
    rule: ConformanceRule,
    context: RuntimeContext
  ): ViolationDetails | null {
    if (!contractSpec.rateLimit) return null;

    const key = `${apiCall.method}:${apiCall.path}`;
    const now = Date.now();
    const window = contractSpec.rateLimit.window;
    
    let tracker = this.rateLimitTracker.get(key);
    
    // Initialize or reset window if needed
    if (!tracker || now - tracker.windowStart > window) {
      tracker = { count: 0, windowStart: now };
      this.rateLimitTracker.set(key, tracker);
    }
    
    tracker.count++;
    
    if (tracker.count > contractSpec.rateLimit.requests) {
      return this.createViolation(
        rule,
        `Rate limit exceeded: ${tracker.count} requests in ${window}ms window (limit: ${contractSpec.rateLimit.requests})`,
        contractSpec.rateLimit.requests,
        tracker.count,
        context,
        apiCall
      );
    }
    
    return null;
  }

  /**
   * Validate data against schema
   */
  private validateSchema(
    data: any,
    schema: any,
    type: 'request' | 'response',
    rule: ConformanceRule,
    context: RuntimeContext,
    apiCall: APICallData
  ): ViolationDetails | null {
    try {
      // Basic schema validation (in production, use proper JSON schema validator)
      if (schema.required) {
        for (const field of schema.required) {
          if (!(field in data)) {
            return this.createViolation(
              rule,
              `Missing required ${type} field: ${field}`,
              schema.required,
              Object.keys(data),
              context,
              apiCall
            );
          }
        }
      }

      if (schema.properties) {
        for (const [field, fieldSchema] of Object.entries(schema.properties as any)) {
          if (field in data) {
            const fieldValue = data[field];
            const expectedType = (fieldSchema as any).type;
            
            if (expectedType && typeof fieldValue !== expectedType) {
              return this.createViolation(
                rule,
                `Invalid ${type} field type for '${field}': expected ${expectedType}, got ${typeof fieldValue}`,
                expectedType,
                typeof fieldValue,
                context,
                apiCall
              );
            }
          }
        }
      }

      return null;

    } catch (error) {
      return this.createViolation(
        rule,
        `Schema validation error: ${error instanceof Error ? error.message : String(error)}`,
        'Valid schema',
        'Invalid data',
        context,
        apiCall,
        error instanceof Error ? error.stack : undefined
      );
    }
  }

  /**
   * Validate path parameters
   */
  private validatePathParameters(
    apiCall: APICallData,
    contractSpec: APIContractSpec,
    rule: ConformanceRule,
    context: RuntimeContext
  ): ViolationDetails | null {
    // Extract path parameters from the contract spec pattern and actual path
    const specPathSegments = contractSpec.path.split('/');
    const actualPathSegments = apiCall.path.split('/');

    if (specPathSegments.length !== actualPathSegments.length) {
      return this.createViolation(
        rule,
        `Path structure mismatch: expected ${specPathSegments.length} segments, got ${actualPathSegments.length}`,
        contractSpec.path,
        apiCall.path,
        context,
        apiCall
      );
    }

    for (let i = 0; i < specPathSegments.length; i++) {
      const specSegment = specPathSegments[i];
      const actualSegment = actualPathSegments[i];

      // Check parameter segments (e.g., {id})
      if (specSegment && specSegment.startsWith('{') && specSegment.endsWith('}')) {
        const paramName = specSegment.slice(1, -1);
        
        // Basic parameter validation (could be enhanced with type checking)
        if (!actualSegment || actualSegment.length === 0) {
          return this.createViolation(
            rule,
            `Missing path parameter: ${paramName}`,
            `Non-empty ${paramName}`,
            actualSegment,
            context,
            apiCall
          );
        }
      } else if (specSegment !== actualSegment) {
        return this.createViolation(
          rule,
          `Path segment mismatch at position ${i}: expected '${specSegment}', got '${actualSegment}'`,
          specSegment,
          actualSegment,
          context,
          apiCall
        );
      }
    }

    return null;
  }

  /**
   * Create violation details
   */
  private createViolation(
    rule: ConformanceRule,
    message: string,
    expectedValue: any,
    actualValue: any,
    context: RuntimeContext,
    apiCall: APICallData,
    stackTrace?: string
  ): ViolationDetails {
    return {
      ruleId: rule.id,
      ruleName: rule.name,
      category: rule.category,
      severity: rule.severity,
      message,
      actualValue,
      expectedValue,
      context,
      stackTrace,
      evidence: {
        inputData: apiCall,
        stateSnapshot: {
          method: apiCall.method,
          path: apiCall.path,
          status: apiCall.response?.status,
          responseTime: apiCall.response?.time
        },
        metrics: {
          responseTime: apiCall.response?.time || 0
        },
        logs: [`API contract violation for ${apiCall.method} ${apiCall.path}`]
      },
      remediation: {
        suggested: this.generateAPISuggestions(rule, apiCall),
        automatic: false,
        priority: this.mapSeverityToPriority(rule.severity)
      }
    };
  }

  /**
   * Generate API-specific suggestions
   */
  private generateAPISuggestions(rule: ConformanceRule, apiCall: APICallData): string[] {
    const suggestions: string[] = [];

    if (rule.condition.expression.includes('method')) {
      suggestions.push('Verify the HTTP method matches the API specification');
    }

    if (rule.condition.expression.includes('status')) {
      suggestions.push('Check API implementation for correct status code handling');
    }

    if (rule.condition.expression.includes('headers')) {
      suggestions.push('Ensure all required headers are included in the request');
    }

    if (rule.condition.expression.includes('timeout')) {
      suggestions.push('Optimize API response time or increase timeout threshold');
    }

    if (rule.condition.expression.includes('schema')) {
      suggestions.push('Validate request/response data against the API schema');
    }

    if (rule.condition.expression.includes('rate_limit')) {
      suggestions.push('Implement proper rate limiting or reduce request frequency');
    }

    if (suggestions.length === 0) {
      suggestions.push('Review API implementation to ensure contract compliance');
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
   * Create common API contract rules
   */
  static createCommonRules(): ConformanceRule[] {
    const now = new Date().toISOString();

    return [
      {
        id: uuidv4(),
        name: 'HTTP Method Compliance',
        description: 'Ensures API calls use the correct HTTP method',
        category: 'api_contract',
        severity: 'major',
        enabled: true,
        condition: {
          expression: 'method',
          variables: ['data'],
          constraints: {}
        },
        actions: ['log_violation'],
        metadata: {
          createdAt: now,
          updatedAt: now,
          version: '1.0.0',
          tags: ['http', 'method']
        }
      },
      {
        id: uuidv4(),
        name: 'Response Status Validation',
        description: 'Validates API response status codes',
        category: 'api_contract',
        severity: 'major',
        enabled: true,
        condition: {
          expression: 'status',
          variables: ['data'],
          constraints: {}
        },
        actions: ['log_violation'],
        metadata: {
          createdAt: now,
          updatedAt: now,
          version: '1.0.0',
          tags: ['status', 'response']
        }
      },
      {
        id: uuidv4(),
        name: 'Response Time Limit',
        description: 'Ensures API responses meet performance requirements',
        category: 'api_contract',
        severity: 'minor',
        enabled: true,
        condition: {
          expression: 'timeout',
          variables: ['data'],
          constraints: {}
        },
        actions: ['log_violation', 'metric_increment'],
        metadata: {
          createdAt: now,
          updatedAt: now,
          version: '1.0.0',
          tags: ['performance', 'timeout']
        }
      },
      {
        id: uuidv4(),
        name: 'Required Headers Check',
        description: 'Validates presence of required HTTP headers',
        category: 'api_contract',
        severity: 'major',
        enabled: true,
        condition: {
          expression: 'headers',
          variables: ['data'],
          constraints: {}
        },
        actions: ['log_violation'],
        metadata: {
          createdAt: now,
          updatedAt: now,
          version: '1.0.0',
          tags: ['headers', 'required']
        }
      }
    ];
  }
}