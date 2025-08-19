/**
 * Integration Testing Types
 * Phase 2.3: Types and interfaces for comprehensive integration testing
 */

import { z } from 'zod';

// Test execution status
export const TestStatusSchema = z.enum([
  'pending',
  'running',
  'passed',
  'failed',
  'skipped',
  'timeout',
  'error'
]);

export type TestStatus = z.infer<typeof TestStatusSchema>;

// Test severity levels
export const TestSeveritySchema = z.enum([
  'critical',
  'major',
  'minor',
  'info'
]);

export type TestSeverity = z.infer<typeof TestSeveritySchema>;

// Test categories
export const TestCategorySchema = z.enum([
  'unit',
  'integration',
  'e2e',
  'performance',
  'security',
  'accessibility',
  'compatibility',
  'regression',
  'smoke',
  'contract'
]);

export type TestCategory = z.infer<typeof TestCategorySchema>;

// Environment configuration
export const TestEnvironmentSchema = z.object({
  name: z.string(),
  baseUrl: z.string().url().optional(),
  apiUrl: z.string().url().optional(),
  database: z.object({
    host: z.string(),
    port: z.number(),
    name: z.string(),
    username: z.string().optional(),
    password: z.string().optional()
  }).optional(),
  variables: z.record(z.string()).default({}),
  timeouts: z.object({
    default: z.number().default(30000),
    api: z.number().default(10000),
    ui: z.number().default(5000),
    database: z.number().default(15000)
  }).default({}),
  retries: z.object({
    max: z.number().default(3),
    delay: z.number().default(1000)
  }).default({})
});

export type TestEnvironment = z.infer<typeof TestEnvironmentSchema>;

// Test fixture definition
export const TestFixtureSchema = z.object({
  id: z.string(),
  name: z.string(),
  description: z.string(),
  category: TestCategorySchema,
  data: z.record(z.any()).default({}),
  setup: z.array(z.string()).default([]),
  teardown: z.array(z.string()).default([]),
  dependencies: z.array(z.string()).default([]),
  metadata: z.object({
    createdAt: z.string().datetime(),
    updatedAt: z.string().datetime(),
    version: z.string().default('1.0.0'),
    tags: z.array(z.string()).default([]),
    author: z.string().optional()
  })
});

export type TestFixture = z.infer<typeof TestFixtureSchema>;

// Test case definition
export const TestCaseSchema = z.object({
  id: z.string(),
  name: z.string(),
  description: z.string(),
  category: TestCategorySchema,
  severity: TestSeveritySchema,
  enabled: z.boolean().default(true),
  preconditions: z.array(z.string()).default([]),
  steps: z.array(z.object({
    id: z.string(),
    description: z.string(),
    action: z.string(),
    data: z.record(z.any()).default({}),
    expectedResult: z.string().optional(),
    timeout: z.number().optional()
  })),
  expectedResults: z.array(z.string()),
  fixtures: z.array(z.string()).default([]),
  dependencies: z.array(z.string()).default([]),
  tags: z.array(z.string()).default([]),
  metadata: z.object({
    estimatedDuration: z.number().optional(),
    complexity: z.enum(['low', 'medium', 'high']).default('medium'),
    stability: z.enum(['stable', 'flaky', 'unstable']).default('stable'),
    lastUpdated: z.string().datetime(),
    maintainer: z.string().optional()
  })
});

export type TestCase = z.infer<typeof TestCaseSchema>;

// Test execution result
export const TestResultSchema = z.object({
  id: z.string(),
  testId: z.string(),
  status: TestStatusSchema,
  startTime: z.string().datetime(),
  endTime: z.string().datetime().optional(),
  duration: z.number(), // milliseconds
  environment: z.string(),
  steps: z.array(z.object({
    id: z.string(),
    status: TestStatusSchema,
    startTime: z.string().datetime(),
    endTime: z.string().datetime().optional(),
    duration: z.number(),
    actualResult: z.string().optional(),
    error: z.string().optional(),
    screenshots: z.array(z.string()).default([]),
    logs: z.array(z.string()).default([]),
    metrics: z.record(z.number()).default({})
  })),
  error: z.string().optional(),
  stackTrace: z.string().optional(),
  screenshots: z.array(z.string()).default([]),
  logs: z.array(z.string()).default([]),
  metrics: z.object({
    memoryUsage: z.number().optional(),
    cpuUsage: z.number().optional(),
    networkCalls: z.number().default(0),
    databaseQueries: z.number().default(0),
    responseTime: z.number().optional(),
    renderTime: z.number().optional()
  }).default({}),
  coverage: z.object({
    lines: z.number().optional(),
    functions: z.number().optional(),
    branches: z.number().optional(),
    statements: z.number().optional()
  }).optional(),
  artifacts: z.array(z.object({
    name: z.string(),
    path: z.string(),
    type: z.enum(['log', 'screenshot', 'video', 'report', 'data']),
    size: z.number().optional()
  })).default([])
});

export type TestResult = z.infer<typeof TestResultSchema>;

// Test suite definition
export const TestSuiteSchema = z.object({
  id: z.string(),
  name: z.string(),
  description: z.string(),
  category: TestCategorySchema,
  tests: z.array(z.string()), // Test case IDs
  fixtures: z.array(z.string()).default([]), // Fixture IDs
  configuration: z.object({
    parallel: z.boolean().default(false),
    maxConcurrency: z.number().default(1),
    timeout: z.number().default(300000), // 5 minutes
    retries: z.number().default(0),
    skipOnFailure: z.boolean().default(false),
    failFast: z.boolean().default(false)
  }).default({}),
  setup: z.array(z.string()).default([]),
  teardown: z.array(z.string()).default([]),
  metadata: z.object({
    estimatedDuration: z.number().optional(),
    priority: z.enum(['low', 'medium', 'high', 'critical']).default('medium'),
    schedule: z.string().optional(), // Cron expression
    owner: z.string().optional(),
    tags: z.array(z.string()).default([])
  })
});

export type TestSuite = z.infer<typeof TestSuiteSchema>;

// Test execution configuration
export const TestExecutionConfigSchema = z.object({
  environment: z.string(),
  parallel: z.boolean().default(false),
  maxConcurrency: z.number().default(4),
  timeout: z.number().default(600000), // 10 minutes
  retries: z.number().default(1),
  skipOnFailure: z.boolean().default(false),
  failFast: z.boolean().default(false),
  generateReport: z.boolean().default(true),
  captureScreenshots: z.boolean().default(true),
  recordVideo: z.boolean().default(false),
  collectLogs: z.boolean().default(true),
  measureCoverage: z.boolean().default(false),
  outputDir: z.string().default('./test-results'),
  reportFormat: z.array(z.enum(['json', 'html', 'xml', 'junit'])).default(['json', 'html']),
  filters: z.object({
    categories: z.array(TestCategorySchema).optional(),
    tags: z.array(z.string()).optional(),
    severity: z.array(TestSeveritySchema).optional(),
    exclude: z.array(z.string()).optional() // Test IDs to exclude
  }).default({})
});

export type TestExecutionConfig = z.infer<typeof TestExecutionConfigSchema>;

// Test execution summary
export const TestExecutionSummarySchema = z.object({
  id: z.string(),
  startTime: z.string().datetime(),
  endTime: z.string().datetime(),
  duration: z.number(),
  environment: z.string(),
  configuration: TestExecutionConfigSchema,
  statistics: z.object({
    total: z.number(),
    passed: z.number(),
    failed: z.number(),
    skipped: z.number(),
    timeout: z.number(),
    error: z.number(),
    passRate: z.number(), // percentage
    coverage: z.object({
      lines: z.number().optional(),
      functions: z.number().optional(),
      branches: z.number().optional(),
      statements: z.number().optional()
    }).optional()
  }),
  results: z.array(TestResultSchema),
  failures: z.array(z.object({
    testId: z.string(),
    testName: z.string(),
    error: z.string(),
    stackTrace: z.string().optional()
  })),
  artifacts: z.array(z.object({
    name: z.string(),
    path: z.string(),
    size: z.number()
  })),
  metadata: z.object({
    nodeVersion: z.string().optional(),
    platform: z.string().optional(),
    browser: z.string().optional(),
    browserVersion: z.string().optional(),
    resolution: z.string().optional(),
    commit: z.string().optional(),
    branch: z.string().optional()
  }).default({})
});

export type TestExecutionSummary = z.infer<typeof TestExecutionSummarySchema>;

// Test runner interface
export interface TestRunner {
  readonly id: string;
  readonly name: string;
  readonly category: TestCategory;
  
  canRun(test: TestCase): boolean;
  runTest(test: TestCase, environment: TestEnvironment): Promise<TestResult>;
  runSuite(suite: TestSuite, environment: TestEnvironment): Promise<TestExecutionSummary>;
  
  // Lifecycle hooks
  setup?(environment: TestEnvironment): Promise<void>;
  teardown?(environment: TestEnvironment): Promise<void>;
  beforeTest?(test: TestCase): Promise<void>;
  afterTest?(test: TestCase, result: TestResult): Promise<void>;
}

// Test reporter interface
export interface TestReporter {
  readonly name: string;
  readonly format: string;
  
  generateReport(summary: TestExecutionSummary): Promise<string>;
  saveReport(content: string, filePath: string): Promise<void>;
}

// Integration test orchestrator configuration
export interface IntegrationTestConfig {
  environments: TestEnvironment[];
  defaultEnvironment: string;
  runners: TestRunner[];
  reporters: TestReporter[];
  globalTimeout: number;
  globalRetries: number;
  parallelSuites: boolean;
  maxSuiteConcurrency: number;
  artifactRetention: {
    days: number;
    maxSize: number; // MB
  };
  notifications: {
    enabled: boolean;
    channels: string[];
    onFailure: boolean;
    onSuccess: boolean;
  };
}

// Test discovery interface
export interface TestDiscovery {
  discoverTests(patterns: string[]): Promise<TestCase[]>;
  discoverSuites(patterns: string[]): Promise<TestSuite[]>;
  discoverFixtures(patterns: string[]): Promise<TestFixture[]>;
}

// Test execution context
export interface TestExecutionContext {
  testId: string;
  suiteId?: string;
  environment: TestEnvironment;
  config: TestExecutionConfig;
  fixtures: Map<string, TestFixture>;
  sharedData: Map<string, any>;
  logger: {
    info: (message: string) => void;
    warn: (message: string) => void;
    error: (message: string) => void;
    debug: (message: string) => void;
  };
  metrics: {
    startTimer: (name: string) => void;
    endTimer: (name: string) => number;
    increment: (name: string, value?: number) => void;
    gauge: (name: string, value: number) => void;
  };
}

// End-to-end test step types
export type E2EStepType = 
  | 'navigate'
  | 'click'
  | 'type'
  | 'select'
  | 'wait'
  | 'verify'
  | 'screenshot'
  | 'custom'
  | 'api_call'
  | 'database_query';

// End-to-end test step
export interface E2ETestStep {
  type: E2EStepType;
  selector?: string;
  value?: string;
  timeout?: number;
  retry?: boolean;
  screenshot?: boolean;
  description: string;
  data?: Record<string, any>;
  validation?: {
    type: 'text' | 'attribute' | 'css' | 'count' | 'exists';
    expected: any;
    actual?: any;
  };
}

// Contract test definition
export interface ContractTest {
  provider: string;
  consumer: string;
  interactions: Array<{
    description: string;
    request: {
      method: string;
      path: string;
      headers?: Record<string, string>;
      body?: any;
    };
    response: {
      status: number;
      headers?: Record<string, string>;
      body?: any;
    };
  }>;
  metadata: {
    version: string;
    createdAt: string;
    tags: string[];
  };
}

// Performance test metrics
export interface PerformanceMetrics {
  responseTime: {
    min: number;
    max: number;
    avg: number;
    p50: number;
    p95: number;
    p99: number;
  };
  throughput: {
    requestsPerSecond: number;
    totalRequests: number;
  };
  resource: {
    cpuUsage: number;
    memoryUsage: number;
    diskIO: number;
    networkIO: number;
  };
  errors: {
    total: number;
    rate: number;
    types: Record<string, number>;
  };
  custom: Record<string, number>;
}