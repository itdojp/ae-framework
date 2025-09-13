/**
 * CEGIS (Counter-Example Guided Inductive Synthesis) Failure Artifact Schema
 * 
 * Standardized schema for capturing and processing failure artifacts
 * to enable automated specification/code repair and synthesis
 */

import { z } from 'zod';

// Severity levels for failures
export const FailureSeveritySchema = z.enum(['critical', 'major', 'minor', 'info']);
export type FailureSeverity = z.infer<typeof FailureSeveritySchema>;

// Failure categories for classification
export const FailureCategorySchema = z.enum([
  'specification_mismatch',
  'contract_violation', 
  'type_error',
  'runtime_error',
  'performance_regression',
  'security_violation',
  'quality_gate_failure',
  'drift_detection',
  'test_failure'
]);
export type FailureCategory = z.infer<typeof FailureCategorySchema>;

// Location information for failures
export const FailureLocationSchema = z.object({
  file: z.string(),
  line: z.number().optional(),
  column: z.number().optional(),
  function: z.string().optional(),
  module: z.string().optional(),
});
export type FailureLocation = z.infer<typeof FailureLocationSchema>;

// Context information for failures
export const FailureContextSchema = z.object({
  environment: z.string().default('development'),
  phase: z.string().optional(), // TDD phase, pipeline stage, etc.
  component: z.string().optional(),
  timestamp: z.string().datetime(),
  commitHash: z.string().optional(),
  branch: z.string().optional(),
  userId: z.string().optional(),
});
export type FailureContext = z.infer<typeof FailureContextSchema>;

// Evidence and diagnostic information
export const FailureEvidenceSchema = z.object({
  stackTrace: z.string().optional(),
  logs: z.array(z.string()).default([]),
  metrics: z.record(z.union([z.string(), z.number(), z.boolean()])).optional(),
  screenshots: z.array(z.string()).default([]), // Base64 or URLs
  networkLogs: z.array(z.object({
    url: z.string(),
    method: z.string(),
    status: z.number().optional(),
    requestBody: z.string().optional(),
    responseBody: z.string().optional(),
  })).default([]),
  environmentInfo: z.record(z.string()).optional(),
});
export type FailureEvidence = z.infer<typeof FailureEvidenceSchema>;

// Suggested fixes and repair actions
export const RepairActionSchema = z.object({
  type: z.enum([
    'code_change',
    'spec_update', 
    'config_change',
    'dependency_update',
    'test_update',
    'documentation_update'
  ]),
  description: z.string(),
  targetFile: z.string().optional(),
  proposedChange: z.string().optional(),
  confidence: z.number().min(0).max(1), // 0-1 confidence score
  reasoning: z.string().optional(),
  prerequisites: z.array(z.string()).default([]),
});
export type RepairAction = z.infer<typeof RepairActionSchema>;

// Root cause analysis
export const RootCauseSchema = z.object({
  hypothesis: z.string(),
  evidence: z.array(z.string()),
  confidence: z.number().min(0).max(1),
  relatedFailures: z.array(z.string()).default([]), // IDs of related failures
});
export type RootCause = z.infer<typeof RootCauseSchema>;

// Main failure artifact schema
export const FailureArtifactSchema = z.object({
  // Unique identifier for this failure
  id: z.string().uuid(),
  
  // Basic failure information
  title: z.string(),
  description: z.string(),
  severity: FailureSeveritySchema,
  category: FailureCategorySchema,
  
  // Location and context
  location: FailureLocationSchema.optional(),
  context: FailureContextSchema,
  
  // Evidence and diagnostics
  evidence: FailureEvidenceSchema,
  
  // Analysis and repair suggestions
  rootCause: RootCauseSchema.optional(),
  suggestedActions: z.array(RepairActionSchema).default([]),
  
  // Metadata
  createdAt: z.string().datetime(),
  updatedAt: z.string().datetime(),
  resolvedAt: z.string().datetime().optional(),
  tags: z.array(z.string()).default([]),
  
  // Relationships
  parentFailureId: z.string().uuid().optional(),
  childFailureIds: z.array(z.string().uuid()).default([]),
  
  // Status tracking
  status: z.enum(['open', 'analyzing', 'fixing', 'testing', 'resolved', 'ignored']).default('open'),
  assignee: z.string().optional(),
  
  // Schema version for evolution
  schemaVersion: z.string().default('1.0.0'),
});

export type FailureArtifact = z.infer<typeof FailureArtifactSchema>;

// Collection schema for multiple failures
export const FailureArtifactCollectionSchema = z.object({
  failures: z.array(FailureArtifactSchema),
  metadata: z.object({
    generatedAt: z.string().datetime(),
    totalCount: z.number(),
    severityCounts: z.record(FailureSeveritySchema, z.number()).optional(),
    categoryCounts: z.record(FailureCategorySchema, z.number()).optional(),
    environment: z.string(),
    source: z.string().optional(),
  }),
  schemaVersion: z.string().default('1.0.0'),
});

export type FailureArtifactCollection = z.infer<typeof FailureArtifactCollectionSchema>;

// Utility functions for creating failure artifacts
export class FailureArtifactFactory {
  static create(base: Partial<FailureArtifact>): FailureArtifact {
    const now = new Date().toISOString();
    const id = base.id || crypto.randomUUID();
    
    return FailureArtifactSchema.parse({
      id,
      title: base.title || 'Unknown Failure',
      description: base.description || 'No description provided',
      severity: base.severity || 'minor',
      category: base.category || 'runtime_error',
      context: {
        timestamp: now,
        environment: 'development',
        ...base.context,
      },
      evidence: base.evidence || {},
      createdAt: now,
      updatedAt: now,
      ...base,
    });
  }

  static fromError(error: Error, context?: Partial<FailureContext>): FailureArtifact {
    return this.create({
      title: error.name || 'Runtime Error',
      description: error.message,
      severity: 'major',
      category: 'runtime_error',
      evidence: {
        stackTrace: error.stack,
        logs: [error.message],
        screenshots: [],
        networkLogs: [],
      },
      ...(context ? {
        context: {
          timestamp: new Date().toISOString(),
          environment: 'development',
          ...context,
        }
      } : {}),
    });
  }

  static fromTestFailure(testName: string, error: string, location?: FailureLocation): FailureArtifact {
    return this.create({
      title: `Test Failure: ${testName}`,
      description: error,
      severity: 'major',
      category: 'test_failure',
      location,
      evidence: {
        logs: [error],
        screenshots: [],
        networkLogs: [],
      },
    });
  }

  static fromContractViolation(
    contractName: string, 
    expected: any, 
    actual: any, 
    location?: FailureLocation
  ): FailureArtifact {
    return this.create({
      title: `Contract Violation: ${contractName}`,
      description: `Expected: ${JSON.stringify(expected)}, Got: ${JSON.stringify(actual)}`,
      severity: 'critical',
      category: 'contract_violation',
      location,
      evidence: {
        logs: [
          `Contract: ${contractName}`,
          `Expected: ${JSON.stringify(expected, null, 2)}`,
          `Actual: ${JSON.stringify(actual, null, 2)}`,
        ],
        screenshots: [],
        networkLogs: [],
      },
      suggestedActions: [
        {
          type: 'spec_update',
          description: 'Update specification to match actual behavior',
          confidence: 0.7,
          reasoning: 'Contract mismatch may indicate specification is outdated',
          prerequisites: [],
        },
        {
          type: 'code_change', 
          description: 'Fix implementation to match specification',
          confidence: 0.8,
          reasoning: 'Implementation should conform to specified contract',
          prerequisites: [],
        },
      ],
    });
  }
}

// Validation utilities
export function validateFailureArtifact(data: unknown): FailureArtifact {
  return FailureArtifactSchema.parse(data);
}

export function validateFailureArtifactCollection(data: unknown): FailureArtifactCollection {
  return FailureArtifactCollectionSchema.parse(data);
}

// Type guards
export function isFailureArtifact(data: unknown): data is FailureArtifact {
  try {
    FailureArtifactSchema.parse(data);
    return true;
  } catch {
    return false;
  }
}
