/**
 * Conformance Verification Engine
 * Phase 2.2: Central orchestrator for runtime conformance verification
 */

import { v4 as uuidv4 } from 'uuid';
import { EventEmitter } from 'events';
import {
  ConformanceRule,
  ConformanceConfig,
  RuntimeContext,
  VerificationResult,
  ViolationDetails,
  ConformanceVerificationResult,
  ConformanceMonitor,
  ViolationHandler,
  ConformanceMetrics,
  ViolationSeverity,
  ConformanceRuleCategory
} from './types.js';
import { ConformanceRuleEngine } from './rule-engine.js';
import { DataValidationMonitor } from './monitors/data-validation-monitor.js';
import { APIContractMonitor } from './monitors/api-contract-monitor.js';

export class ConformanceVerificationEngine extends EventEmitter {
  private config: ConformanceConfig;
  private ruleEngine: ConformanceRuleEngine;
  private monitors: Map<string, ConformanceMonitor> = new Map();
  private violationHandlers: Map<ConformanceRuleCategory, ViolationHandler[]> = new Map();
  private metrics: ConformanceMetrics;
  private isRunning = false;
  private verificationCount = 0;
  private violationCount = 0;

  constructor(config: ConformanceConfig) {
    super();
    this.config = config;
    this.ruleEngine = new ConformanceRuleEngine(config);
    this.metrics = this.initializeMetrics();
    
    this.setupDefaultMonitors();
  }

  /**
   * Start the verification engine
   */
  async start(): Promise<void> {
    if (this.isRunning) {
      throw new Error('Verification engine is already running');
    }

    this.isRunning = true;
    this.emit('started', { timestamp: new Date().toISOString() });
    
    // Start periodic metrics collection
    this.startMetricsCollection();
  }

  /**
   * Stop the verification engine
   */
  async stop(): Promise<void> {
    if (!this.isRunning) {
      return;
    }

    this.isRunning = false;
    this.emit('stopped', { timestamp: new Date().toISOString() });
  }

  /**
   * Verify data against all applicable rules
   */
  async verify(
    data: any,
    context: RuntimeContext,
    options?: {
      ruleIds?: string[];
      skipCategories?: ConformanceRuleCategory[];
      async?: boolean;
    }
  ): Promise<ConformanceVerificationResult> {
    if (!this.isRunning) {
      throw new Error('Verification engine is not running');
    }

    const executionId = uuidv4();
    const startTime = Date.now();

    try {
      this.verificationCount++;

      // Enhanced context with execution info
      const enhancedContext: RuntimeContext = {
        ...context,
        executionId,
        metadata: {
          ...context.metadata,
          engineVersion: '2.2.0',
          verificationId: executionId
        }
      };

      // Use rule engine for primary verification
      let result = await this.ruleEngine.verifyConformance(
        data,
        enhancedContext,
        options?.ruleIds
      );

      // Filter out skipped categories if specified
      if (options?.skipCategories?.length) {
        result.results = result.results.filter(r => {
          const rule = this.ruleEngine.getRules().find(rule => rule.id === r.ruleId);
          return !rule || !options.skipCategories!.includes(rule.category);
        });
        
        result.violations = result.violations.filter(v => 
          !options.skipCategories!.includes(v.category)
        );
      }

      // Run specialized monitors for additional verification
      const monitorResults = await this.runSpecializedMonitors(data, enhancedContext);
      
      // Merge monitor results
      result = this.mergeResults(result, monitorResults);

      // Handle violations
      if (result.violations.length > 0) {
        this.violationCount += result.violations.length;
        
        if (options?.async !== false) {
          // Handle violations asynchronously by default
          setImmediate(() => this.handleViolationsAsync(result.violations, enhancedContext));
        } else {
          // Handle violations synchronously if requested
          await this.handleViolationsSync(result.violations, enhancedContext);
        }
      }

      // Update metrics
      this.updateMetrics(result, Date.now() - startTime);

      // Emit verification event
      this.emit('verification_completed', {
        executionId,
        result,
        duration: Date.now() - startTime
      });

      return result;

    } catch (error) {
      const errorResult: ConformanceVerificationResult = {
        overall: 'error',
        results: [{
          id: uuidv4(),
          ruleId: 'engine-error',
          status: 'error',
          timestamp: new Date().toISOString(),
          duration: Date.now() - startTime,
          context,
          violation: {
            ruleId: 'engine-error',
            ruleName: 'Verification Engine Error',
            category: 'data_validation',
            severity: 'critical',
            message: `Verification failed: ${error instanceof Error ? error.message : String(error)}`,
            context,
            stackTrace: error instanceof Error ? error.stack : undefined,
            evidence: { inputData: data }
          },
          metrics: { executionTime: Date.now() - startTime }
        }],
        violations: [],
        summary: {
          totalRules: 0,
          rulesExecuted: 0,
          rulesPassed: 0,
          rulesFailed: 0,
          rulesSkipped: 0,
          rulesError: 1,
          totalDuration: Date.now() - startTime,
          violationsBySeverity: { critical: 0, major: 0, minor: 0, info: 0, warning: 0 },
          violationsByCategory: {
            data_validation: 0, api_contract: 0, business_logic: 0, security_policy: 0,
            performance_constraint: 0, resource_usage: 0, state_invariant: 0,
            behavioral_constraint: 0, integration_requirement: 0, compliance_rule: 0
          }
        },
        metadata: {
          executionId,
          timestamp: new Date().toISOString(),
          environment: this.config.performance?.maxConcurrentChecks ? 'production' : 'development',
          version: '2.2.0'
        }
      };

      this.emit('verification_error', { executionId, error, result: errorResult });
      return errorResult;
    }
  }

  /**
   * Add a conformance rule
   */
  async addRule(rule: ConformanceRule): Promise<void> {
    await this.ruleEngine.addRule(rule);
    
    // Also add to relevant monitors
    for (const monitor of this.monitors.values()) {
      if (monitor.canVerify(rule.id)) {
        await monitor.updateRule(rule);
      }
    }

    this.emit('rule_added', { ruleId: rule.id, category: rule.category });
  }

  /**
   * Update a conformance rule
   */
  async updateRule(rule: ConformanceRule): Promise<void> {
    await this.ruleEngine.updateRule(rule);
    
    // Update in relevant monitors
    for (const monitor of this.monitors.values()) {
      if (monitor.canVerify(rule.id)) {
        await monitor.updateRule(rule);
      }
    }

    this.emit('rule_updated', { ruleId: rule.id, category: rule.category });
  }

  /**
   * Remove a conformance rule
   */
  async removeRule(ruleId: string): Promise<void> {
    await this.ruleEngine.removeRule(ruleId);
    
    // Remove from monitors
    for (const monitor of this.monitors.values()) {
      if (monitor.canVerify(ruleId)) {
        await monitor.removeRule(ruleId);
      }
    }

    this.emit('rule_removed', { ruleId });
  }

  /**
   * Get all rules
   */
  getRules(): ConformanceRule[] {
    return this.ruleEngine.getRules();
  }

  /**
   * Get rules by category
   */
  getRulesByCategory(category: ConformanceRuleCategory): ConformanceRule[] {
    return this.ruleEngine.getRulesByCategory(category);
  }

  /**
   * Add a specialized monitor
   */
  addMonitor(monitor: ConformanceMonitor): void {
    this.monitors.set(monitor.id, monitor);
    this.emit('monitor_added', { monitorId: monitor.id, monitorName: monitor.name });
  }

  /**
   * Remove a specialized monitor
   */
  removeMonitor(monitorId: string): void {
    const monitor = this.monitors.get(monitorId);
    if (monitor) {
      this.monitors.delete(monitorId);
      this.emit('monitor_removed', { monitorId, monitorName: monitor.name });
    }
  }

  /**
   * Add a violation handler
   */
  addViolationHandler(category: ConformanceRuleCategory, handler: ViolationHandler): void {
    if (!this.violationHandlers.has(category)) {
      this.violationHandlers.set(category, []);
    }
    
    const handlers = this.violationHandlers.get(category)!;
    handlers.push(handler);
    
    // Sort by priority (higher priority first)
    handlers.sort((a, b) => b.priority - a.priority);

    this.emit('handler_added', { category, handlerCount: handlers.length });
  }

  /**
   * Remove a violation handler
   */
  removeViolationHandler(category: ConformanceRuleCategory, handler: ViolationHandler): void {
    const handlers = this.violationHandlers.get(category);
    if (handlers) {
      const index = handlers.indexOf(handler);
      if (index !== -1) {
        handlers.splice(index, 1);
        this.emit('handler_removed', { category, handlerCount: handlers.length });
      }
    }
  }

  /**
   * Get current metrics
   */
  getMetrics(): ConformanceMetrics {
    return {
      ...this.metrics,
      timestamp: new Date().toISOString()
    };
  }

  /**
   * Reset metrics
   */
  resetMetrics(): void {
    this.metrics = this.initializeMetrics();
    this.verificationCount = 0;
    this.violationCount = 0;
    this.emit('metrics_reset');
  }

  /**
   * Get engine configuration
   */
  getConfig(): ConformanceConfig {
    return { ...this.config };
  }

  /**
   * Update engine configuration
   */
  updateConfig(newConfig: Partial<ConformanceConfig>): void {
    this.config = { ...this.config, ...newConfig };
    this.emit('config_updated', { config: this.config });
  }

  /**
   * Setup default monitors
   */
  private setupDefaultMonitors(): void {
    // Add data validation monitor
    const dataMonitor = new DataValidationMonitor();
    this.addMonitor(dataMonitor);

    // Add API contract monitor  
    const apiMonitor = new APIContractMonitor();
    this.addMonitor(apiMonitor);

    // Load default rules for each monitor
    const dataRules = DataValidationMonitor.createCommonRules();
    const apiRules = APIContractMonitor.createCommonRules();

    Promise.all([
      ...dataRules.map(rule => this.addRule(rule)),
      ...apiRules.map(rule => this.addRule(rule))
    ]).catch(error => {
      console.warn('Failed to load default rules:', error);
    });
  }

  /**
   * Run specialized monitors
   */
  private async runSpecializedMonitors(
    data: any,
    context: RuntimeContext
  ): Promise<VerificationResult[]> {
    const results: VerificationResult[] = [];

    for (const monitor of this.monitors.values()) {
      try {
        const result = await monitor.verify(data, context);
        results.push(result);
      } catch (error) {
        // Create error result for failed monitor
        results.push({
          id: uuidv4(),
          ruleId: `${monitor.id}-error`,
          status: 'error',
          timestamp: new Date().toISOString(),
          duration: 0,
          context,
          violation: {
            ruleId: `${monitor.id}-error`,
            ruleName: `${monitor.name} Error`,
            category: 'data_validation',
            severity: 'major',
            message: `Monitor execution failed: ${error instanceof Error ? error.message : String(error)}`,
            context,
            stackTrace: error instanceof Error ? error.stack : undefined,
            evidence: { inputData: data }
          },
          metrics: { executionTime: 0 }
        });
      }
    }

    return results;
  }

  /**
   * Merge results from different sources
   */
  private mergeResults(
    primary: ConformanceVerificationResult,
    additional: VerificationResult[]
  ): ConformanceVerificationResult {
    // Merge results arrays
    const allResults = [...primary.results, ...additional];
    
    // Merge violations
    const allViolations = [
      ...primary.violations,
      ...additional.filter(r => r.violation).map(r => r.violation!)
    ];

    // Recalculate summary
    const summary = this.calculateSummary(allResults, allViolations);
    
    // Determine overall status
    const overall = this.determineOverallStatus(allResults);

    return {
      ...primary,
      overall,
      results: allResults,
      violations: allViolations,
      summary
    };
  }

  /**
   * Handle violations asynchronously
   */
  private async handleViolationsAsync(violations: ViolationDetails[], context: RuntimeContext): Promise<void> {
    try {
      for (const violation of violations) {
        await this.handleSingleViolation(violation, context);
      }
    } catch (error) {
      this.emit('violation_handling_error', { error, context });
    }
  }

  /**
   * Handle violations synchronously
   */
  private async handleViolationsSync(violations: ViolationDetails[], context: RuntimeContext): Promise<void> {
    for (const violation of violations) {
      await this.handleSingleViolation(violation, context);
    }
  }

  /**
   * Handle a single violation
   */
  private async handleSingleViolation(violation: ViolationDetails, context: RuntimeContext): Promise<void> {
    const handlers = this.violationHandlers.get(violation.category) || [];
    
    for (const handler of handlers) {
      if (handler.canHandle(violation)) {
        try {
          await handler.handle(violation, context);
          this.emit('violation_handled', { 
            violation: violation.ruleId, 
            handler: handler.constructor.name 
          });
        } catch (error) {
          this.emit('violation_handler_error', { 
            violation: violation.ruleId, 
            handler: handler.constructor.name,
            error 
          });
        }
      }
    }

    // Always emit violation event for monitoring
    this.emit('violation_detected', { violation, context });
  }

  /**
   * Calculate result summary
   */
  private calculateSummary(results: VerificationResult[], violations: ViolationDetails[]) {
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

  /**
   * Determine overall status from results
   */
  private determineOverallStatus(results: VerificationResult[]) {
    if (results.some(r => r.status === 'error')) return 'error' as const;
    if (results.some(r => r.status === 'fail')) return 'fail' as const;
    if (results.every(r => r.status === 'skip')) return 'skip' as const;
    return 'pass' as const;
  }

  /**
   * Update metrics with verification result
   */
  private updateMetrics(result: ConformanceVerificationResult, duration: number): void {
    this.metrics.counts.totalVerifications++;
    this.metrics.counts.totalViolations += result.violations.length;
    this.metrics.counts.uniqueRules = this.getRules().length;

    // Update performance metrics
    this.metrics.performance.averageExecutionTime = 
      (this.metrics.performance.averageExecutionTime * (this.verificationCount - 1) + duration) / this.verificationCount;

    // Simple p95/p99 estimation (in production, use proper percentile calculation)
    this.metrics.performance.p95ExecutionTime = Math.max(this.metrics.performance.p95ExecutionTime, duration * 0.95);
    this.metrics.performance.p99ExecutionTime = Math.max(this.metrics.performance.p99ExecutionTime, duration * 0.99);

    if (result.overall === 'error') {
      this.metrics.performance.errors++;
    }
  }

  /**
   * Initialize metrics structure
   */
  private initializeMetrics(): ConformanceMetrics {
    const now = new Date().toISOString();
    
    return {
      timestamp: now,
      period: {
        start: now,
        end: now
      },
      counts: {
        totalVerifications: 0,
        totalViolations: 0,
        uniqueRules: 0,
        uniqueViolations: 0
      },
      performance: {
        averageExecutionTime: 0,
        p95ExecutionTime: 0,
        p99ExecutionTime: 0,
        timeouts: 0,
        errors: 0
      },
      violationTrends: [],
      topViolations: []
    };
  }

  /**
   * Start periodic metrics collection
   */
  private startMetricsCollection(): void {
    if (this.config.reporting?.flushIntervalMs) {
      const interval = setInterval(() => {
        if (!this.isRunning) {
          clearInterval(interval);
          return;
        }

        this.emit('metrics_collected', this.getMetrics());
        
        // Reset period counters but keep cumulative data
        this.metrics.period.start = this.metrics.period.end;
        this.metrics.period.end = new Date().toISOString();
        
      }, this.config.reporting.flushIntervalMs);
    }
  }
}