/**
 * Runtime Conformance Verification Types
 * Phase 2.2: Types and schemas for runtime behavior monitoring and verification
 */

import { z } from 'zod';

// Conformance rule categories
export const ConformanceRuleCategorySchema = z.enum([
  'data_validation',
  'api_contract',
  'business_logic',
  'security_policy',
  'performance_constraint',
  'resource_usage',
  'state_invariant',
  'behavioral_constraint',
  'integration_requirement',
  'compliance_rule'
]);

export type ConformanceRuleCategory = z.infer<typeof ConformanceRuleCategorySchema>;

// Severity levels for violations
export const ViolationSeveritySchema = z.enum([
  'critical',
  'major', 
  'minor',
  'info',
  'warning'
]);

export type ViolationSeverity = z.infer<typeof ViolationSeveritySchema>;

// Verification result status
export const VerificationStatusSchema = z.enum([
  'pass',
  'fail', 
  'skip',
  'error',
  'timeout'
]);

export type VerificationStatus = z.infer<typeof VerificationStatusSchema>;

// Context information for runtime verification
export const RuntimeContextSchema = z.object({
  timestamp: z.string().datetime(),
  executionId: z.string().uuid(),
  functionName: z.string().optional(),
  modulePath: z.string().optional(),
  requestId: z.string().optional(),
  userId: z.string().optional(),
  sessionId: z.string().optional(),
  environment: z.string().default('development'),
  version: z.string().optional(),
  buildId: z.string().optional(),
  traceId: z.string().optional(),
  spanId: z.string().optional(),
  metadata: z.record(z.any()).default({})
});

export type RuntimeContext = z.infer<typeof RuntimeContextSchema>;

// Conformance rule definition
export const ConformanceRuleSchema = z.object({
  id: z.string().uuid(),
  name: z.string().min(1).max(200),
  description: z.string().min(1).max(1000),
  category: ConformanceRuleCategorySchema,
  severity: ViolationSeveritySchema,
  enabled: z.boolean().default(true),
  condition: z.object({
    expression: z.string(), // JavaScript-like expression
    variables: z.array(z.string()).default([]),
    constraints: z.record(z.any()).default({})
  }),
  actions: z.array(z.enum([
    'log_violation',
    'throw_error',
    'return_default',
    'circuit_break',
    'alert',
    'metric_increment',
    'trace_event'
  ])).default(['log_violation']),
  metadata: z.object({
    createdAt: z.string().datetime(),
    updatedAt: z.string().datetime(),
    version: z.string().default('1.0.0'),
    tags: z.array(z.string()).default([]),
    owner: z.string().optional(),
    documentation: z.string().optional()
  })
});

export type ConformanceRule = z.infer<typeof ConformanceRuleSchema>;

// Violation details
export const ViolationDetailsSchema = z.object({
  ruleId: z.string().uuid(),
  ruleName: z.string(),
  category: ConformanceRuleCategorySchema,
  severity: ViolationSeveritySchema,
  message: z.string(),
  actualValue: z.any().optional(),
  expectedValue: z.any().optional(),
  context: RuntimeContextSchema,
  stackTrace: z.string().optional(),
  evidence: z.object({
    inputData: z.any().optional(),
    outputData: z.any().optional(),
    stateSnapshot: z.record(z.any()).default({}),
    metrics: z.record(z.number()).default({}),
    logs: z.array(z.string()).default([]),
    traces: z.array(z.any()).default([])
  }).default({}),
  remediation: z.object({
    suggested: z.array(z.string()).default([]),
    automatic: z.boolean().default(false),
    priority: z.enum(['low', 'medium', 'high', 'critical']).default('medium')
  }).optional()
});

export type ViolationDetails = z.infer<typeof ViolationDetailsSchema>;

// Verification result
export const VerificationResultSchema = z.object({
  id: z.string().uuid(),
  ruleId: z.string().uuid(),
  status: VerificationStatusSchema,
  timestamp: z.string().datetime(),
  duration: z.number(), // milliseconds
  context: RuntimeContextSchema,
  violation: ViolationDetailsSchema.optional(),
  metrics: z.object({
    executionTime: z.number(),
    memoryUsage: z.number().optional(),
    cpuUsage: z.number().optional(),
    networkCalls: z.number().default(0),
    dbQueries: z.number().default(0)
  }).default({ executionTime: 0, networkCalls: 0, dbQueries: 0 }),
  metadata: z.record(z.any()).default({})
});

export type VerificationResult = z.infer<typeof VerificationResultSchema>;

// Conformance verification configuration
export const ConformanceConfigSchema = z.object({
  enabled: z.boolean().default(true),
  mode: z.enum(['strict', 'permissive', 'monitor_only']).default('permissive'),
  rules: z.array(z.string().uuid()).default([]),
  sampling: z.object({
    enabled: z.boolean().default(false),
    rate: z.number().min(0).max(1).default(1.0),
    strategy: z.enum(['random', 'systematic', 'adaptive']).default('random')
  }).default({}),
  performance: z.object({
    timeoutMs: z.number().default(5000),
    maxConcurrentChecks: z.number().default(10),
    cacheResults: z.boolean().default(true),
    cacheTtlMs: z.number().default(300000) // 5 minutes
  }).default({}),
  reporting: z.object({
    destinations: z.array(z.enum([
      'console',
      'file',
      'metrics',
      'database',
      'webhook'
    ])).default(['console']),
    batchSize: z.number().default(100),
    flushIntervalMs: z.number().default(30000)
  }).default({}),
  alerting: z.object({
    enabled: z.boolean().default(false),
    thresholds: z.record(z.number()).default({}),
    channels: z.array(z.string()).default([])
  }).default({})
});

export type ConformanceConfig = z.infer<typeof ConformanceConfigSchema>;

// Runtime monitor interface
export interface ConformanceMonitor {
  readonly id: string;
  readonly name: string;
  
  verify(data: any, context: RuntimeContext): Promise<VerificationResult>;
  canVerify(ruleId: string): boolean;
  getRules(): ConformanceRule[];
  updateRule(rule: ConformanceRule): Promise<void>;
  removeRule(ruleId: string): Promise<void>;
}

// Violation handler interface
export interface ViolationHandler {
  readonly category: ConformanceRuleCategory;
  readonly priority: number;
  
  handle(violation: ViolationDetails, context: RuntimeContext): Promise<void>;
  canHandle(violation: ViolationDetails): boolean;
}

// Conformance verification engine result
export interface ConformanceVerificationResult {
  overall: VerificationStatus;
  results: VerificationResult[];
  violations: ViolationDetails[];
  summary: {
    totalRules: number;
    rulesExecuted: number;
    rulesPassed: number;
    rulesFailed: number;
    rulesSkipped: number;
    rulesError: number;
    totalDuration: number;
    violationsBySeverity: Record<ViolationSeverity, number>;
    violationsByCategory: Record<ConformanceRuleCategory, number>;
  };
  metadata: {
    executionId: string;
    timestamp: string;
    environment: string;
    version: string;
  };
}

// Rule execution context
export interface RuleExecutionContext {
  rule: ConformanceRule;
  input: any;
  output?: any;
  runtime: RuntimeContext;
  config: ConformanceConfig;
  cache: Map<string, any>;
}

// Pattern matching for common violations
export interface ViolationPattern {
  id: string;
  name: string;
  category: ConformanceRuleCategory;
  pattern: RegExp | string;
  confidence: number;
  description: string;
  suggestedFix?: string;
}

// Conformance metrics
export interface ConformanceMetrics {
  timestamp: string;
  period: {
    start: string;
    end: string;
  };
  counts: {
    totalVerifications: number;
    totalViolations: number;
    uniqueRules: number;
    uniqueViolations: number;
  };
  performance: {
    averageExecutionTime: number;
    p95ExecutionTime: number;
    p99ExecutionTime: number;
    timeouts: number;
    errors: number;
  };
  violationTrends: {
    category: ConformanceRuleCategory;
    severity: ViolationSeverity;
    count: number;
    trend: 'increasing' | 'decreasing' | 'stable';
  }[];
  topViolations: {
    ruleId: string;
    ruleName: string;
    count: number;
    lastOccurrence: string;
  }[];
}
