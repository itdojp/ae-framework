/**
 * Quality Policy Loader and Manager
 * Centralized system for loading and managing quality gates from policy.json
 */

import * as fs from 'fs';
import * as path from 'path';
import { z } from 'zod';

// Type definitions for Quality Policy
export const QualityThresholdSchema = z.object({
  minScore: z.number().optional(),
  maxViolations: z.number().optional(),
  blockOnCritical: z.boolean().optional(),
  blockOnFail: z.boolean().optional(),
  // Coverage specific
  lines: z.number().optional(),
  functions: z.number().optional(),
  branches: z.number().optional(),
  statements: z.number().optional(),
  // Performance specific
  maxResponseTime: z.number().optional(),
  minThroughput: z.number().optional(),
  maxMemoryUsage: z.string().optional(),
  // Lighthouse specific
  performance: z.number().optional(),
  accessibility: z.number().optional(),
  bestPractices: z.number().optional(),
  seo: z.number().optional(),
  // Security specific
  maxCritical: z.number().optional(),
  maxHigh: z.number().optional(),
  maxMedium: z.number().optional(),
  // Linting specific
  maxErrors: z.number().optional(),
  maxWarnings: z.number().optional(),
  blockOnErrors: z.boolean().optional(),
  // TDD specific
  minTestsPerFunction: z.number().optional(),
  maxCyclomaticComplexity: z.number().optional(),
  // API specific
  schemaComplianceScore: z.number().optional(),
  maxContractViolations: z.number().optional(),
});

export const QualityGateSchema = z.object({
  name: z.string(),
  description: z.string(),
  category: z.string(),
  enabled: z.boolean(),
  thresholds: z.record(QualityThresholdSchema),
  tools: z.array(z.string()),
  commands: z.object({
    test: z.string(),
    report: z.string().optional(),
    fix: z.string().optional(),
  }),
});

export const EnvironmentConfigSchema = z.object({
  description: z.string(),
  enforcementLevel: z.enum(['warning', 'strict', 'blocking']),
});

export const CompositeGateSchema = z.object({
  description: z.string(),
  gates: z.array(z.string()),
  environments: z.array(z.string()),
});

export const QualityPolicySchema = z.object({
  version: z.string(),
  lastUpdated: z.string(),
  description: z.string(),
  environments: z.record(EnvironmentConfigSchema),
  qualityGates: z.record(QualityGateSchema),
  compositeGates: z.record(CompositeGateSchema),
  integrations: z.object({
    ci: z.object({
      githubActions: z.object({
        enabled: z.boolean(),
        workflow: z.string(),
        triggerOn: z.array(z.string()),
        parallelExecution: z.boolean(),
      }),
      preCommitHooks: z.object({
        enabled: z.boolean(),
        hooks: z.array(z.string()),
        blocking: z.boolean(),
      }),
    }),
    monitoring: z.object({
      opentelemetry: z.object({
        enabled: z.boolean(),
        metricsPrefix: z.string(),
        tracingEnabled: z.boolean(),
      }),
      dashboards: z.record(z.any()),
    }),
  }),
  notifications: z.record(z.any()),
  reporting: z.object({
    formats: z.array(z.string()),
    outputDirectory: z.string(),
    retention: z.object({
      days: z.number(),
      maxReports: z.number(),
    }),
    aggregation: z.object({
      enabled: z.boolean(),
      interval: z.string(),
      metrics: z.array(z.string()),
    }),
  }),
});

export type QualityThreshold = z.infer<typeof QualityThresholdSchema>;
export type QualityGate = z.infer<typeof QualityGateSchema>;
export type EnvironmentConfig = z.infer<typeof EnvironmentConfigSchema>;
export type CompositeGate = z.infer<typeof CompositeGateSchema>;
export type QualityPolicy = z.infer<typeof QualityPolicySchema>;

export interface QualityGateResult {
  gateName: string;
  passed: boolean;
  score?: number;
  violations: string[];
  executionTime: number;
  environment: string;
  threshold: QualityThreshold;
  details?: Record<string, any>;
}

export interface QualityReport {
  timestamp: string;
  environment: string;
  overallScore: number;
  totalGates: number;
  passedGates: number;
  failedGates: number;
  results: QualityGateResult[];
  summary: {
    byCategory: Record<string, { passed: number; total: number }>;
    executionTime: number;
    blockers: string[];
  };
}

export class QualityPolicyLoader {
  private policy: QualityPolicy | null = null;
  private policyPath: string;

  constructor(policyPath?: string) {
    this.policyPath = policyPath || path.join(process.cwd(), 'config', 'quality-policy.json');
  }

  /**
   * Load quality policy from JSON file
   */
  public loadPolicy(): QualityPolicy {
    if (this.policy) {
      return this.policy;
    }

    try {
      if (!fs.existsSync(this.policyPath)) {
        throw new Error(`Quality policy file not found at: ${this.policyPath}`);
      }

      const policyContent = fs.readFileSync(this.policyPath, 'utf8');
      const policyData = JSON.parse(policyContent);
      
      const validationResult = QualityPolicySchema.safeParse(policyData);
      if (!validationResult.success) {
        throw new Error(`Invalid quality policy schema: ${validationResult.error.message}`);
      }

      this.policy = validationResult.data;
      return this.policy;
    } catch (error) {
      throw new Error(`Failed to load quality policy: ${error}`);
    }
  }

  /**
   * Get quality gates for specific environment
   */
  public getGatesForEnvironment(environment: string = 'development'): QualityGate[] {
    const policy = this.loadPolicy();
    
    // Find composite gate for environment
    const compositeGate = Object.values(policy.compositeGates)
      .find(gate => gate.environments.includes(environment));

    if (!compositeGate) {
      // Fallback to all enabled gates
      return Object.values(policy.qualityGates).filter(gate => gate.enabled);
    }

    return compositeGate.gates
      .map(gateName => policy.qualityGates[gateName])
      .filter((gate): gate is QualityGate => Boolean(gate && gate.enabled));
  }

  /**
   * Get threshold for specific gate and environment
   */
  public getThreshold(gateName: string, environment: string = 'development'): QualityThreshold {
    const policy = this.loadPolicy();
    const gate = policy.qualityGates[gateName];
    
    if (!gate) {
      throw new Error(`Quality gate '${gateName}' not found in policy`);
    }

    const threshold = gate.thresholds[environment];
    if (!threshold) {
      // Fallback to development environment
      const fallbackThreshold = gate.thresholds['development'];
      if (!fallbackThreshold) {
        throw new Error(`No threshold found for gate '${gateName}' in environment '${environment}'`);
      }
      return fallbackThreshold;
    }

    return threshold;
  }

  /**
   * Check if gate should block on failure for environment
   */
  public shouldBlock(gateName: string, environment: string = 'development'): boolean {
    const policy = this.loadPolicy();
    const envConfig = policy.environments[environment];
    const threshold = this.getThreshold(gateName, environment);

    // Check environment-level enforcement
    if (envConfig?.enforcementLevel === 'blocking') {
      return true;
    }

    // Check gate-specific threshold
    return threshold.blockOnFail === true || threshold.blockOnCritical === true || threshold.blockOnErrors === true;
  }

  /**
   * Get environment configuration
   */
  public getEnvironmentConfig(environment: string): EnvironmentConfig {
    const policy = this.loadPolicy();
    const envConfig = policy.environments[environment];
    
    if (!envConfig) {
      // Return default development configuration
      return policy.environments['development'] || {
        description: 'Default environment',
        enforcementLevel: 'warning',
      };
    }

    return envConfig;
  }

  /**
   * Get all available quality gates
   */
  public getAllGates(): Record<string, QualityGate> {
    const policy = this.loadPolicy();
    return policy.qualityGates;
  }

  /**
   * Get composite gate definition
   */
  public getCompositeGate(gateName: string): CompositeGate | null {
    const policy = this.loadPolicy();
    return policy.compositeGates[gateName] || null;
  }

  /**
   * Get integration settings
   */
  public getIntegrations(): QualityPolicy['integrations'] {
    const policy = this.loadPolicy();
    return policy.integrations;
  }

  /**
   * Get reporting configuration
   */
  public getReportingConfig(): QualityPolicy['reporting'] {
    const policy = this.loadPolicy();
    return policy.reporting;
  }

  /**
   * Validate gate result against thresholds
   */
  public validateGateResult(
    gateName: string,
    result: Partial<QualityGateResult>,
    environment: string = 'development'
  ): { passed: boolean; violations: string[] } {
    const threshold = this.getThreshold(gateName, environment);
    const violations: string[] = [];

    // Score-based validation
    if (threshold.minScore !== undefined && result.score !== undefined) {
      if (result.score < threshold.minScore) {
        violations.push(`Score ${result.score} below minimum ${threshold.minScore}`);
      }
    }

    // Coverage validation
    if (result.details) {
      const { lines, functions, branches, statements } = result.details;
      
      if (threshold.lines !== undefined && lines !== undefined && lines < threshold.lines) {
        violations.push(`Line coverage ${lines}% below minimum ${threshold.lines}%`);
      }
      
      if (threshold.functions !== undefined && functions !== undefined && functions < threshold.functions) {
        violations.push(`Function coverage ${functions}% below minimum ${threshold.functions}%`);
      }
      
      if (threshold.branches !== undefined && branches !== undefined && branches < threshold.branches) {
        violations.push(`Branch coverage ${branches}% below minimum ${threshold.branches}%`);
      }
      
      if (threshold.statements !== undefined && statements !== undefined && statements < threshold.statements) {
        violations.push(`Statement coverage ${statements}% below minimum ${threshold.statements}%`);
      }
    }

    // Violation count validation
    if (threshold.maxViolations !== undefined && result.violations) {
      if (result.violations.length > threshold.maxViolations) {
        violations.push(`Too many violations: ${result.violations.length} > ${threshold.maxViolations}`);
      }
    }

    const passed = violations.length === 0;
    return { passed, violations };
  }

  /**
   * Generate quality report
   */
  public generateReport(results: QualityGateResult[], environment: string): QualityReport {
    const timestamp = new Date().toISOString();
    const totalGates = results.length;
    const passedGates = results.filter(r => r.passed).length;
    const failedGates = totalGates - passedGates;
    
    // Calculate overall score
    const scoresWithValues = results.filter(r => r.score !== undefined);
    const overallScore = scoresWithValues.length > 0
      ? Math.round(scoresWithValues.reduce((sum, r) => sum + (r.score || 0), 0) / scoresWithValues.length)
      : 0;

    // Group by category
    const byCategory: Record<string, { passed: number; total: number }> = {};
    const policy = this.loadPolicy();
    
    for (const result of results) {
      const gate = policy.qualityGates[result.gateName];
      if (gate) {
        const category = gate.category;
        if (!byCategory[category]) {
          byCategory[category] = { passed: 0, total: 0 };
        }
        byCategory[category].total++;
        if (result.passed) {
          byCategory[category].passed++;
        }
      }
    }

    // Find blockers
    const blockers = results
      .filter(r => !r.passed && this.shouldBlock(r.gateName, environment))
      .map(r => r.gateName);

    return {
      timestamp,
      environment,
      overallScore,
      totalGates,
      passedGates,
      failedGates,
      results,
      summary: {
        byCategory,
        executionTime: results.reduce((sum, r) => sum + r.executionTime, 0),
        blockers,
      },
    };
  }

  /**
   * Export policy as different formats
   */
  public exportPolicy(format: 'json' | 'yaml' | 'summary' = 'json'): string {
    const policy = this.loadPolicy();

    switch (format) {
      case 'json':
        return JSON.stringify(policy, null, 2);
      
      case 'yaml':
        // Simple YAML export (would need yaml library for full implementation)
        return JSON.stringify(policy, null, 2);
      
      case 'summary':
        const gates = Object.keys(policy.qualityGates);
        const environments = Object.keys(policy.environments);
        const composites = Object.keys(policy.compositeGates);
        
        return `Quality Policy Summary
Version: ${policy.version}
Last Updated: ${policy.lastUpdated}

Environments (${environments.length}): ${environments.join(', ')}
Quality Gates (${gates.length}): ${gates.join(', ')}
Composite Gates (${composites.length}): ${composites.join(', ')}

Description: ${policy.description}`;
      
      default:
        return JSON.stringify(policy, null, 2);
    }
  }
}

// Global instance for easy access
export const qualityPolicy = new QualityPolicyLoader();
