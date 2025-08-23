/**
 * CEGIS (Counter-Example Guided Inductive Synthesis) Types
 * Phase 2.1: Core types for failure artifacts and auto-fix system
 */

import { z } from 'zod';

// Failure categories for classification
export const FailureCategorySchema = z.enum([
  'contract_violation',
  'test_failure', 
  'type_error',
  'runtime_error',
  'build_error',
  'lint_error',
  'security_violation',
  'performance_issue',
  'accessibility_violation',
  'dependency_issue'
]);

export type FailureCategory = z.infer<typeof FailureCategorySchema>;

// Code location information
export const CodeLocationSchema = z.object({
  filePath: z.string(),
  startLine: z.number(),
  endLine: z.number(),
  startColumn: z.number().optional(),
  endColumn: z.number().optional(),
  functionName: z.string().optional(),
  className: z.string().optional()
});

export type CodeLocation = z.infer<typeof CodeLocationSchema>;

// Failure context information
export const FailureContextSchema = z.object({
  environment: z.string().default('development'),
  nodeVersion: z.string().optional(),
  timestamp: z.string().datetime(),
  phase: z.enum(['intent', 'formal', 'test', 'code', 'verify', 'operate']).optional(),
  command: z.string().optional(),
  workingDirectory: z.string().optional(),
  gitCommit: z.string().optional(),
  gitBranch: z.string().optional()
});

export type FailureContext = z.infer<typeof FailureContextSchema>;

// Evidence and diagnostic information
export const FailureEvidenceSchema = z.object({
  stackTrace: z.string().optional(),
  errorMessage: z.string().optional(),
  errorType: z.string().optional(),
  logs: z.array(z.string()).default([]),
  metrics: z.record(z.number()).default({}),
  sourceCode: z.string().optional(),
  testOutput: z.string().optional(),
  buildOutput: z.string().optional(),
  lintOutput: z.string().optional(),
  dependencies: z.array(z.string()).default([]),
  relatedFiles: z.array(z.string()).default([])
});

export type FailureEvidence = z.infer<typeof FailureEvidenceSchema>;

// Root cause analysis
export const RootCauseSchema = z.object({
  primaryCause: z.string(),
  contributingFactors: z.array(z.string()).default([]),
  confidence: z.number().min(0).max(1),
  reasoning: z.string(),
  suggestedActions: z.array(z.string()).default([])
});

export type RootCause = z.infer<typeof RootCauseSchema>;

// Repair action specification
export const RepairActionSchema = z.object({
  type: z.enum([
    'code_change',
    'dependency_update',
    'config_change',
    'test_update',
    'documentation_update',
    'refactor',
    'type_annotation',
    'validation_update'
  ]),
  description: z.string(),
  confidence: z.number().min(0).max(1),
  riskLevel: z.number().min(1).max(5),
  estimatedEffort: z.enum(['low', 'medium', 'high']),
  filePath: z.string().optional(),
  codeChange: z.object({
    oldCode: z.string(),
    newCode: z.string(),
    startLine: z.number(),
    endLine: z.number()
  }).optional(),
  dependencies: z.array(z.string()).default([]),
  prerequisites: z.array(z.string()).default([])
});

export type RepairAction = z.infer<typeof RepairActionSchema>;

// Core failure artifact schema
export const FailureArtifactSchema = z.object({
  id: z.string().uuid(),
  title: z.string().min(1).max(200),
  description: z.string().min(1).max(2000),
  severity: z.enum(['critical', 'major', 'minor', 'info']),
  category: FailureCategorySchema,
  location: CodeLocationSchema.optional(),
  context: FailureContextSchema,
  evidence: FailureEvidenceSchema,
  rootCause: RootCauseSchema.optional(),
  suggestedActions: z.array(RepairActionSchema).default([]),
  relatedArtifacts: z.array(z.string().uuid()).default([]),
  metadata: z.object({
    createdAt: z.string().datetime(),
    updatedAt: z.string().datetime(),
    version: z.string().default('1.0.0'),
    tags: z.array(z.string()).default([]),
    environment: z.record(z.string()).optional(),
    source: z.string().default('cegis_system')
  })
});

export type FailureArtifact = z.infer<typeof FailureArtifactSchema>;

// Fix strategy types
export interface FixStrategy {
  name: string;
  category: FailureCategory;
  confidence: number;
  riskLevel: number;
  description: string;
  canApply: (failure: FailureArtifact) => Promise<boolean>;
  generateFix: (failure: FailureArtifact) => Promise<RepairAction[]>;
}

// Applied fix result
export interface AppliedFix {
  strategy: string;
  actions: RepairAction[];
  success: boolean;
  filesModified: string[];
  errors: string[];
  warnings: string[];
  type?: string;
  description?: string;
  targetFile?: string;
  confidence?: number;
  metadata: {
    timestamp: string;
    duration: number;
    confidence: number;
    riskLevel: number;
  };
}

// Skipped fix information
export interface SkippedFix {
  strategy: string;
  reason: string;
  confidence?: number;
  riskLevel?: number;
  error?: string;
}

// Auto-fix configuration
export interface AutoFixConfig {
  dryRun: boolean;
  confidenceThreshold: number;
  maxRiskLevel: number;
  enabledCategories: FailureCategory[];
  maxFixesPerRun: number;
  timeoutMs: number;
  backupFiles: boolean;
  generateReport: boolean;
}

// Fix execution result
export interface FixResult {
  appliedFixes: AppliedFix[];
  skippedFixes: SkippedFix[];
  summary: {
    totalFailures: number;
    fixesApplied: number;
    fixesSkipped: number;
    filesModified: number;
    success: boolean;
    errors: string[];
    warnings: string[];
  };
  recommendations: string[];
  reportPath?: string;
  success: boolean;
  appliedActions: AppliedFix[];
  generatedFiles: string[];
  backupFiles: string[];
  errors: string[];
}

// Risk assessment result
export interface RiskAssessment {
  level: number; // 1-5 scale
  factors: string[];
  mitigation: string[];
  recommendation: 'proceed' | 'caution' | 'abort';
}

// Auto-fix options for CLI
export interface AutoFixOptions {
  dryRun?: boolean;
  confidenceThreshold?: number;
  maxRiskLevel?: number;
  timeoutMs?: number;
  maxIterations?: number;
  outputDir?: string;
}

// Pattern analysis result
export interface FailurePattern {
  pattern: string;
  frequency: number;
  categories: FailureCategory[];
  commonLocations: CodeLocation[];
  suggestedStrategies: string[];
  confidence: number;
}