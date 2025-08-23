/**
 * Conformance Rule Engine
 * Phase 2.2: Core engine for executing conformance rules and detecting violations
 */

import { v4 as uuidv4 } from 'uuid';
import { 
  ConformanceRule,
  ConformanceConfig,
  RuntimeContext,
  VerificationResult,
  VerificationStatus,
  ViolationDetails,
  RuleExecutionContext,
  ConformanceVerificationResult,
  ViolationSeverity,
  ConformanceRuleCategory
} from './types.js';

export class ConformanceRuleEngine {
  private rules: Map<string, ConformanceRule> = new Map();
  private config: ConformanceConfig;
  private executionCache: Map<string, VerificationResult> = new Map();
  private metrics: Map<string, number> = new Map();

  constructor(config: ConformanceConfig) {
    this.config = config;
  }

  /**
   * Add a conformance rule to the engine
   */
  async addRule(rule: ConformanceRule): Promise<void> {
    this.rules.set(rule.id, rule);
  }

  /**
   * Remove a rule from the engine
   */
  async removeRule(ruleId: string): Promise<void> {
    this.rules.delete(ruleId);
    this.clearRuleCache(ruleId);
  }

  /**
   * Update an existing rule
   */
  async updateRule(rule: ConformanceRule): Promise<void> {
    this.rules.set(rule.id, rule);
    this.clearRuleCache(rule.id);
  }

  /**
   * Get all loaded rules
   */
  getRules(): ConformanceRule[] {
    return Array.from(this.rules.values());
  }

  /**
   * Get rules by category
   */
  getRulesByCategory(category: ConformanceRuleCategory): ConformanceRule[] {
    return Array.from(this.rules.values()).filter(rule => rule.category === category);
  }

  /**
   * Verify data against all applicable rules
   */
  async verifyConformance(
    data: any,
    context: RuntimeContext,
    ruleIds?: string[]
  ): Promise<ConformanceVerificationResult> {
    const executionId = uuidv4();
    const startTime = Date.now();
    
    // Determine which rules to execute
    const rulesToExecute = this.selectRules(ruleIds);
    
    // Apply sampling if configured
    const sampledRules = this.applySampling(rulesToExecute, context);
    
    // Execute rules concurrently with limits
    const results = await this.executeRulesParallel(
      sampledRules,
      data,
      context,
      executionId
    );
    
    // Collect violations
    const violations = results
      .filter(result => result.violation)
      .map(result => result.violation!);
    
    // Generate summary
    const summary = this.generateSummary(results, violations);
    
    // Create final result
    const verificationResult: ConformanceVerificationResult = {
      overall: this.determineOverallStatus(results),
      results,
      violations,
      summary,
      metadata: {
        executionId,
        timestamp: new Date().toISOString(),
        environment: this.config.performance?.maxConcurrentChecks ? 'production' : 'development',
        version: '2.2.0'
      }
    };

    // Update metrics
    this.updateMetrics(verificationResult, Date.now() - startTime);

    return verificationResult;
  }

  /**
   * Verify a single rule
   */
  async verifyRule(
    ruleId: string,
    data: any,
    context: RuntimeContext
  ): Promise<VerificationResult> {
    const rule = this.rules.get(ruleId);
    if (!rule) {
      throw new Error(`Rule not found: ${ruleId}`);
    }

    if (!rule.enabled) {
      return this.createSkippedResult(rule, context, 'Rule disabled');
    }

    return await this.executeRule(rule, data, context);
  }

  /**
   * Execute a single conformance rule
   */
  private async executeRule(
    rule: ConformanceRule,
    data: any,
    context: RuntimeContext,
    executionId?: string
  ): Promise<VerificationResult> {
    const startTime = Date.now();
    const resultId = uuidv4();

    try {
      // Check cache if enabled
      if (this.config.performance?.cacheResults) {
        const cacheKey = this.generateCacheKey(rule, data, context);
        const cached = this.executionCache.get(cacheKey);
        if (cached && this.isCacheValid(cached)) {
          return { ...cached, id: resultId };
        }
      }

      // Create execution context
      const execContext: RuleExecutionContext = {
        rule,
        input: data,
        runtime: context,
        config: this.config,
        cache: new Map()
      };

      // Execute rule with timeout
      const timeoutMs = this.config.performance?.timeoutMs || 5000;
      const result = await this.executeWithTimeout(
        () => this.evaluateRule(execContext),
        timeoutMs
      );

      const duration = Date.now() - startTime;

      // Create verification result
      const verificationResult: VerificationResult = {
        id: resultId,
        ruleId: rule.id,
        status: result.violated ? 'fail' : 'pass',
        timestamp: new Date().toISOString(),
        duration,
        context,
        violation: result.violated ? result.violation : undefined,
        metrics: {
          executionTime: duration,
          memoryUsage: this.getMemoryUsage(),
          networkCalls: 0,
          dbQueries: 0
        }
      };

      // Cache result if enabled
      if (this.config.performance?.cacheResults) {
        const cacheKey = this.generateCacheKey(rule, data, context);
        this.executionCache.set(cacheKey, verificationResult);
      }

      return verificationResult;

    } catch (error) {
      const duration = Date.now() - startTime;
      
      return {
        id: resultId,
        ruleId: rule.id,
        status: 'error',
        timestamp: new Date().toISOString(),
        duration,
        context,
        violation: {
          ruleId: rule.id,
          ruleName: rule.name,
          category: rule.category,
          severity: rule.severity,
          message: `Rule execution failed: ${error instanceof Error ? error.message : String(error)}`,
          context,
          stackTrace: error instanceof Error ? error.stack : undefined,
          evidence: {}
        },
        metrics: {
          executionTime: duration
        }
      };
    }
  }

  /**
   * Evaluate rule condition against data
   */
  private async evaluateRule(execContext: RuleExecutionContext): Promise<{
    violated: boolean;
    violation?: ViolationDetails;
  }> {
    const { rule, input, runtime } = execContext;
    
    try {
      // Build evaluation context
      const evalContext = {
        data: input,
        context: runtime,
        rule: rule,
        // Helper functions for rule expressions
        validators: this.getValidatorHelpers(),
        utils: this.getUtilityHelpers()
      };

      // Evaluate rule condition
      const conditionResult = await this.evaluateCondition(
        rule.condition.expression,
        evalContext
      );

      // If condition fails, create violation
      if (!conditionResult.passed) {
        const violation: ViolationDetails = {
          ruleId: rule.id,
          ruleName: rule.name,
          category: rule.category,
          severity: rule.severity,
          message: conditionResult.message || `Rule violation: ${rule.name}`,
          actualValue: conditionResult.actualValue,
          expectedValue: conditionResult.expectedValue,
          context: runtime,
          evidence: {
            inputData: input,
            stateSnapshot: conditionResult.state || {},
            metrics: conditionResult.metrics || {},
            logs: conditionResult.logs || []
          },
          remediation: {
            suggested: this.generateRemediationSuggestions(rule, conditionResult),
            automatic: false,
            priority: this.mapSeverityToPriority(rule.severity)
          }
        };

        return { violated: true, violation };
      }

      return { violated: false };

    } catch (error) {
      // Rule evaluation error - treat as violation
      const violation: ViolationDetails = {
        ruleId: rule.id,
        ruleName: rule.name,
        category: rule.category,
        severity: 'major',
        message: `Rule evaluation error: ${error instanceof Error ? error.message : String(error)}`,
        context: runtime,
        stackTrace: error instanceof Error ? error.stack : undefined,
        evidence: {
          inputData: input
        }
      };

      return { violated: true, violation };
    }
  }

  /**
   * Evaluate a condition expression
   */
  private async evaluateCondition(
    expression: string,
    context: any
  ): Promise<{
    passed: boolean;
    message?: string;
    actualValue?: any;
    expectedValue?: any;
    state?: Record<string, any>;
    metrics?: Record<string, number>;
    logs?: string[];
  }> {
    // This is a simplified evaluation - in production, you'd want a safer eval
    // using a proper expression parser/evaluator like expr-eval or similar
    
    try {
      // Create a safe evaluation context
      const safeContext = {
        ...context,
        // Prevent access to dangerous globals
        global: undefined,
        process: undefined,
        require: undefined,
        module: undefined,
        console: {
          log: (msg: string) => context.logs?.push(msg)
        }
      };

      // Simple expression evaluation (replace with proper parser in production)
      const result = this.safeEvaluate(expression, safeContext);
      
      return {
        passed: Boolean(result),
        actualValue: result,
        expectedValue: true
      };

    } catch (error) {
      return {
        passed: false,
        message: `Expression evaluation failed: ${error instanceof Error ? error.message : String(error)}`,
        actualValue: error,
        expectedValue: true
      };
    }
  }

  /**
   * Safe expression evaluation (simplified)
   */
  private safeEvaluate(expression: string, context: any): any {
    // This is a very basic implementation
    // In production, use a proper expression evaluator like expr-eval
    
    const allowedPatterns = [
      /^data\./,
      /^context\./,
      /^validators\./,
      /^utils\./
    ];

    // Check if expression uses only allowed patterns
    const tokens = expression.split(/\s+/);
    for (const token of tokens) {
      if (token.includes('.') && !allowedPatterns.some(pattern => pattern.test(token))) {
        throw new Error(`Unsafe expression: ${token}`);
      }
    }

    // Simple property access evaluation
    if (expression.startsWith('data.')) {
      const path = expression.substring(5);
      return this.getNestedProperty(context.data, path);
    }

    if (expression.startsWith('context.')) {
      const path = expression.substring(8);
      return this.getNestedProperty(context.context, path);
    }

    // Boolean expressions
    if (expression === 'true') return true;
    if (expression === 'false') return false;

    // Default to true for unrecognized expressions (permissive mode)
    return true;
  }

  /**
   * Get nested property from object
   */
  private getNestedProperty(obj: any, path: string): any {
    return path.split('.').reduce((current, prop) => {
      return current && current[prop];
    }, obj);
  }

  /**
   * Execute rules in parallel with concurrency limits
   */
  private async executeRulesParallel(
    rules: ConformanceRule[],
    data: any,
    context: RuntimeContext,
    executionId: string
  ): Promise<VerificationResult[]> {
    const maxConcurrent = this.config.performance?.maxConcurrentChecks || 10;
    const results: VerificationResult[] = [];
    
    // Execute rules in batches
    for (let i = 0; i < rules.length; i += maxConcurrent) {
      const batch = rules.slice(i, i + maxConcurrent);
      const batchPromises = batch.map(rule => 
        this.executeRule(rule, data, context, executionId)
      );
      
      const batchResults = await Promise.allSettled(batchPromises);
      
      // Collect results, handling rejections
      for (const result of batchResults) {
        if (result.status === 'fulfilled') {
          results.push(result.value);
        } else {
          // Create error result for failed execution
          results.push({
            id: uuidv4(),
            ruleId: 'unknown',
            status: 'error',
            timestamp: new Date().toISOString(),
            duration: 0,
            context,
            violation: {
              ruleId: 'unknown',
              ruleName: 'Unknown Rule',
              category: 'data_validation',
              severity: 'major',
              message: `Rule execution failed: ${result.reason}`,
              context,
              evidence: {}
            },
            metrics: { executionTime: 0 }
          });
        }
      }
    }

    return results;
  }

  /**
   * Select rules to execute based on configuration
   */
  private selectRules(ruleIds?: string[]): ConformanceRule[] {
    if (ruleIds) {
      return ruleIds
        .map(id => this.rules.get(id))
        .filter((rule): rule is ConformanceRule => rule !== undefined);
    }

    // Use configured rule list or all rules
    if (this.config.rules && this.config.rules.length > 0) {
      return this.config.rules
        .map(id => this.rules.get(id))
        .filter((rule): rule is ConformanceRule => rule !== undefined && rule.enabled);
    }

    return Array.from(this.rules.values()).filter(rule => rule.enabled);
  }

  /**
   * Apply sampling configuration
   */
  private applySampling(rules: ConformanceRule[], context: RuntimeContext): ConformanceRule[] {
    if (!this.config.sampling?.enabled || this.config.sampling.rate >= 1.0) {
      return rules;
    }

    const sampleSize = Math.ceil(rules.length * this.config.sampling.rate);
    
    switch (this.config.sampling.strategy) {
      case 'random':
        return this.shuffleArray([...rules]).slice(0, sampleSize);
      case 'systematic':
        const step = Math.floor(rules.length / sampleSize);
        return rules.filter((_, index) => index % step === 0);
      case 'adaptive':
        // Prioritize rules that have failed recently
        return rules
          .sort((a, b) => this.getRuleFailureRate(b.id) - this.getRuleFailureRate(a.id))
          .slice(0, sampleSize);
      default:
        return rules.slice(0, sampleSize);
    }
  }

  /**
   * Helper methods
   */
  private executeWithTimeout<T>(
    operation: () => Promise<T>,
    timeoutMs: number
  ): Promise<T> {
    return Promise.race([
      operation(),
      new Promise<T>((_, reject) => 
        setTimeout(() => reject(new Error('Operation timeout')), timeoutMs)
      )
    ]);
  }

  private createSkippedResult(
    rule: ConformanceRule,
    context: RuntimeContext,
    reason: string
  ): VerificationResult {
    return {
      id: uuidv4(),
      ruleId: rule.id,
      status: 'skip',
      timestamp: new Date().toISOString(),
      duration: 0,
      context,
      metrics: { executionTime: 0 },
      metadata: { skipReason: reason }
    };
  }

  private generateCacheKey(rule: ConformanceRule, data: any, context: RuntimeContext): string {
    return `${rule.id}:${JSON.stringify(data)}:${context.timestamp}`;
  }

  private isCacheValid(cached: VerificationResult): boolean {
    const cacheTtl = this.config.performance?.cacheTtlMs || 300000;
    const age = Date.now() - new Date(cached.timestamp).getTime();
    return age < cacheTtl;
  }

  private clearRuleCache(ruleId: string): void {
    for (const [key, result] of this.executionCache.entries()) {
      if (result.ruleId === ruleId) {
        this.executionCache.delete(key);
      }
    }
  }

  private getMemoryUsage(): number {
    if (typeof process !== 'undefined' && process.memoryUsage) {
      return process.memoryUsage().heapUsed;
    }
    return 0;
  }

  private getValidatorHelpers() {
    return {
      isEmail: (value: string) => /^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(value),
      isUrl: (value: string) => {
        try {
          new URL(value);
          return true;
        } catch {
          return false;
        }
      },
      isNumber: (value: any) => typeof value === 'number' && !isNaN(value),
      isString: (value: any) => typeof value === 'string',
      isBoolean: (value: any) => typeof value === 'boolean',
      isArray: (value: any) => Array.isArray(value),
      isObject: (value: any) => typeof value === 'object' && value !== null && !Array.isArray(value),
      hasLength: (value: any, min: number, max?: number) => {
        const length = value?.length ?? 0;
        return length >= min && (max === undefined || length <= max);
      },
      inRange: (value: number, min: number, max: number) => value >= min && value <= max
    };
  }

  private getUtilityHelpers() {
    return {
      now: () => new Date(),
      timestamp: () => Date.now(),
      uuid: uuidv4,
      hash: (value: string) => {
        // Simple hash function - use crypto in production
        let hash = 0;
        for (let i = 0; i < value.length; i++) {
          const char = value.charCodeAt(i);
          hash = ((hash << 5) - hash) + char;
          hash = hash & hash; // Convert to 32-bit integer
        }
        return hash.toString();
      }
    };
  }

  private generateRemediationSuggestions(rule: ConformanceRule, result: any): string[] {
    const suggestions: string[] = [];

    // Generic suggestions based on rule category
    switch (rule.category) {
      case 'data_validation':
        suggestions.push('Validate input data before processing');
        suggestions.push('Add type checking and sanitization');
        break;
      case 'api_contract':
        suggestions.push('Review API specification');
        suggestions.push('Update client/server contract');
        break;
      case 'security_policy':
        suggestions.push('Review security configuration');
        suggestions.push('Update access controls');
        break;
      case 'performance_constraint':
        suggestions.push('Optimize performance-critical code');
        suggestions.push('Review resource usage');
        break;
    }

    return suggestions;
  }

  private mapSeverityToPriority(severity: ViolationSeverity): 'low' | 'medium' | 'high' | 'critical' {
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

  private determineOverallStatus(results: VerificationResult[]): VerificationStatus {
    if (results.some(r => r.status === 'error')) return 'error';
    if (results.some(r => r.status === 'fail')) return 'fail';
    if (results.every(r => r.status === 'skip')) return 'skip';
    return 'pass';
  }

  private generateSummary(results: VerificationResult[], violations: ViolationDetails[]) {
    const violationsBySeverity: Record<ViolationSeverity, number> = {
      critical: 0, major: 0, minor: 0, info: 0, warning: 0
    };
    
    const violationsByCategory: Record<ConformanceRuleCategory, number> = {
      data_validation: 0, api_contract: 0, business_logic: 0, security_policy: 0,
      performance_constraint: 0, resource_usage: 0, state_invariant: 0,
      behavioral_constraint: 0, integration_requirement: 0, compliance_rule: 0
    };

    violations.forEach(v => {
      violationsBySeverity[v.severity]++;
      violationsByCategory[v.category]++;
    });

    return {
      totalRules: results.length,
      rulesExecuted: results.filter(r => r.status !== 'skip').length,
      rulesPassed: results.filter(r => r.status === 'pass').length,
      rulesFailed: results.filter(r => r.status === 'fail').length,
      rulesSkipped: results.filter(r => r.status === 'skip').length,
      rulesError: results.filter(r => r.status === 'error').length,
      totalDuration: results.reduce((sum, r) => sum + r.duration, 0),
      violationsBySeverity,
      violationsByCategory
    };
  }

  private updateMetrics(result: ConformanceVerificationResult, totalDuration: number): void {
    this.metrics.set('total_verifications', (this.metrics.get('total_verifications') || 0) + 1);
    this.metrics.set('total_violations', (this.metrics.get('total_violations') || 0) + result.violations.length);
    this.metrics.set('total_duration', (this.metrics.get('total_duration') || 0) + totalDuration);
  }

  private getRuleFailureRate(ruleId: string): number {
    // Simplified - would track actual failure rates in production
    return Math.random();
  }

  private shuffleArray<T>(array: T[]): T[] {
    const shuffled = [...array];
    for (let i = shuffled.length - 1; i > 0; i--) {
      const j = Math.floor(Math.random() * (i + 1));
      const temp = shuffled[i];
      shuffled[i] = shuffled[j]!;
      shuffled[j] = temp;
    }
    return shuffled;
  }

  /**
   * Get engine metrics
   */
  getMetrics(): Record<string, number> {
    return Object.fromEntries(this.metrics);
  }

  /**
   * Reset engine metrics
   */
  resetMetrics(): void {
    this.metrics.clear();
  }
}