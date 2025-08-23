/**
 * @fileoverview Domain Types for Unified Agent System
 * Phase 2: Agent System Refactoring - Domain Modeling Implementation
 * Core domain types for unified agent architecture per ae-framework-v2.yml
 */

/**
 * Task types supported by the unified agent system
 */
export enum TaskType {
  INTENT_ANALYSIS = 'intent-analysis',
  FORMAL_SPECIFICATION = 'formal-specification', 
  TEST_GENERATION = 'test-generation',
  CODE_GENERATION = 'code-generation',
  VERIFICATION = 'verification',
  VALIDATION = 'validation',
  DEPLOYMENT = 'deployment',
  QUALITY_ASSURANCE = 'quality-assurance',
  PHASE_VALIDATION = 'phase-validation'
}

/**
 * Task specification structure for unified processing
 */
export interface TaskSpecification {
  requirements: string;
  acceptance: string[];
  context: Record<string, any>;
}

/**
 * Unified task definition for all agent types
 */
export interface AgentTask {
  id: string;
  type: TaskType;
  specification: TaskSpecification;
  metadata: {
    priority: number;
    estimatedComplexity: number;
    dependencies?: string[];
    deadline?: Date;
  };
}

/**
 * Task execution result with validation
 */
export interface TaskResult {
  success: boolean;
  taskId: string;
  artifacts: string[];
  validation: {
    typeScriptCompliant: boolean;
    strictModeCompatible?: boolean;
    errorCount: number;
    testsPassing?: boolean;
  };
  tddCompliance?: {
    testsFirst: boolean;
    redPhaseCompleted: boolean;
    greenPhaseCompleted: boolean;
    refactorPhaseCompleted?: boolean;
  };
  metrics?: {
    testCoverage: number;
    executionTime: number;
    qualityScore: number;
  };
  phaseValidation?: {
    readyForNextPhase: boolean;
    completionCriteria: string[];
  };
  errors?: string[];
}

/**
 * Agent context for phase and project state
 */
export interface AgentContext {
  projectRoot: string;
  phase: string;
  tddEnabled: boolean;
  strictMode?: boolean;
  coverageThreshold?: number;
}

/**
 * Unified agent configuration
 */
export interface AgentConfig {
  id: string;
  type: string;
  capabilities: string[];
  context: AgentContext;
}

/**
 * Agent state for lifecycle management
 */
export interface AgentState {
  initialized: boolean;
  currentTask?: string;
  tasksCompleted: number;
  totalExecutionTime: number;
  averageQualityScore: number;
}

/**
 * Quality metrics for agent output validation
 */
export interface QualityMetrics {
  testCoverage: number;
  codeComplexity: number;
  typeScriptErrors: number;
  lintWarnings: number;
  performanceScore: number;
}

/**
 * Validation result structure
 */
export interface ValidationResult {
  success: boolean;
  message: string;
  details: Array<{
    check: string;
    passed: boolean;
    message: string;
    value?: any;
  }>;
}