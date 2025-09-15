# Phase 3.1 API Reference Guide

> 🌍 Language / 言語: English | 日本語

## Overview

This document provides a comprehensive API reference for Phase 3.1 Evidence-based Validation System components. All APIs are designed following TypeScript best practices and provide comprehensive type safety.

---

## Table of Contents

1. [Sequential Inference Engine API](#sequential-inference-engine-api)
2. [Complex Problem Solving Framework API](#complex-problem-solving-framework-api)
3. [Dependency Analysis System API](#dependency-analysis-system-api)
4. [Event System API](#event-system-api)
5. [Configuration API](#configuration-api)
6. [Error Handling](#error-handling)
7. [Type Definitions](#type-definitions)
8. [Usage Examples](#usage-examples)

---

## Sequential Inference Engine API

### Class: SequentialInferenceEngine

**Location**: `src/engines/sequential-inference-engine.ts`

#### Constructor

```typescript
new SequentialInferenceEngine(options?: {
  maxSteps?: number;
  defaultTimeout?: number;
  enableCaching?: boolean;
})
```

**Parameters:**
- `options.maxSteps` (number, optional): Maximum inference steps. Default: 50
- `options.defaultTimeout` (number, optional): Default timeout per step in ms. Default: 30000
- `options.enableCaching` (boolean, optional): Enable result caching. Default: true

#### Methods

##### processComplexQuery()

```typescript
async processComplexQuery(query: ComplexQuery): Promise<InferenceResult>
```

Processes a complex query through multiple inference steps.

**Parameters:**
- `query` (ComplexQuery): The query to process

**Returns:** Promise\<InferenceResult\>

**Example:**
```typescript
const result = await engine.processComplexQuery({
  id: 'query-001',
  description: 'Analyze system dependencies',
  context: { projectPath: '/path/to/project' },
  priority: 'high'
});
```

**Throws:**
- `InvalidQueryError`: When query validation fails
- `TimeoutError`: When processing exceeds timeout
- `InferenceError`: When inference process fails

##### executeInferenceStep()

```typescript
async executeInferenceStep(
  step: InferenceStep, 
  context: ExecutionContext
): Promise<StepResult>
```

Executes a single inference step with given context.

**Parameters:**
- `step` (InferenceStep): The step to execute
- `context` (ExecutionContext): Execution context

**Returns:** Promise\<StepResult\>

##### analyzeDeepDependencies()

```typescript
async analyzeDeepDependencies(
  analysis: DependencyAnalysisRequest
): Promise<DependencyResult>
```

Performs deep dependency analysis using inference engine.

**Parameters:**
- `analysis` (DependencyAnalysisRequest): Analysis configuration

**Returns:** Promise\<DependencyResult\>

##### evaluateImpactScope()

```typescript
async evaluateImpactScope(changes: ChangeSet): Promise<ImpactAnalysis>
```

Evaluates the impact scope of proposed changes.

**Parameters:**
- `changes` (ChangeSet): Set of changes to analyze

**Returns:** Promise\<ImpactAnalysis\>

#### Events

The Sequential Inference Engine extends EventEmitter and emits the following events:

- `stepStarted`: Emitted when inference step starts
- `stepCompleted`: Emitted when inference step completes
- `stepFailed`: Emitted when inference step fails
- `inferenceCompleted`: Emitted when entire inference completes

---

## Complex Problem Solving Framework API

### Class: ProblemDecomposer

**Location**: `src/inference/core/problem-decomposer.ts`

#### Constructor

```typescript
new ProblemDecomposer()
```

#### Methods

##### decompose()

```typescript
async decompose(problem: Problem): Promise<DecompositionResult>
```

Decomposes a complex problem into manageable sub-problems.

**Parameters:**
- `problem` (Problem): The problem to decompose

**Returns:** Promise\<DecompositionResult\>

**Example:**
```typescript
const result = await decomposer.decompose({
  id: 'problem-001',
  title: 'System Optimization',
  description: 'Optimize system performance',
  domain: 'software_development',
  complexity: 'high',
  priority: 'critical',
  constraints: [],
  context: { codebase: '/path/to/code' }
});
```

##### registerDecompositionStrategy()

```typescript
registerDecompositionStrategy(
  domain: string, 
  strategy: (problem: Problem) => SubProblem[]
): void
```

Registers a custom decomposition strategy for a specific domain.

**Parameters:**
- `domain` (string): Domain identifier
- `strategy` (function): Decomposition strategy function

##### registerComplexityAnalyzer()

```typescript
registerComplexityAnalyzer(
  domain: string, 
  analyzer: (problem: Problem) => number
): void
```

Registers a custom complexity analyzer for a specific domain.

**Parameters:**
- `domain` (string): Domain identifier
- `analyzer` (function): Complexity analysis function

### Class: SolutionComposer

**Location**: `src/inference/core/solution-composer.ts`

#### Constructor

```typescript
new SolutionComposer()
```

#### Methods

##### compose()

```typescript
async compose(
  subSolutions: SubSolution[], 
  decompositionResult: DecompositionResult,
  context?: Partial<CompositionContext>
): Promise<CompositeSolution>
```

Composes sub-solutions into a complete solution.

**Parameters:**
- `subSolutions` (SubSolution[]): Array of sub-solutions
- `decompositionResult` (DecompositionResult): Original decomposition result
- `context` (Partial\<CompositionContext\>, optional): Composition context

**Returns:** Promise\<CompositeSolution\>

##### registerCompositionStrategy()

```typescript
registerCompositionStrategy(strategy: CompositionStrategy): void
```

Registers a custom composition strategy.

**Parameters:**
- `strategy` (CompositionStrategy): Composition strategy

##### registerValidator()

```typescript
registerValidator(
  name: string, 
  validator: (result: any, context: CompositionContext) => Promise<ValidationResult[]>
): void
```

Registers a custom validator.

**Parameters:**
- `name` (string): Validator name
- `validator` (function): Validator function

### Class: ValidationOrchestrator

**Location**: `src/inference/core/validation-orchestrator.ts`

#### Constructor

```typescript
new ValidationOrchestrator(options?: {
  maxConcurrentValidations?: number;
  defaultTimeout?: number;
  enableMetrics?: boolean;
})
```

#### Methods

##### createValidationPlan()

```typescript
async createValidationPlan(
  target: any,
  context: ValidationContext,
  requirements?: {
    categories?: ValidationCategory[];
    criticalityLevel?: 'low' | 'medium' | 'high' | 'critical';
    maxDuration?: number;
  }
): Promise<ValidationPlan>
```

Creates a validation plan for the given target.

**Parameters:**
- `target` (any): Target to validate
- `context` (ValidationContext): Validation context
- `requirements` (object, optional): Validation requirements

**Returns:** Promise\<ValidationPlan\>

##### executeValidationPlan()

```typescript
async executeValidationPlan(
  planId: string,
  target: any,
  context: ValidationContext
): Promise<ValidationExecution>
```

Executes a validation plan.

**Parameters:**
- `planId` (string): Plan identifier
- `target` (any): Target to validate
- `context` (ValidationContext): Validation context

**Returns:** Promise\<ValidationExecution\>

##### registerValidator()

```typescript
registerValidator(validator: Validator): void
```

Registers a custom validator.

**Parameters:**
- `validator` (Validator): Validator implementation

---

## Dependency Analysis System API

### Class: DependencyAnalyzer

**Location**: `src/analysis/dependency-analyzer.ts`

#### Constructor

```typescript
new DependencyAnalyzer(options?: {
  cacheSize?: number;
  cacheTTL?: number;
  maxConcurrentAnalyses?: number;
  enableRealTimeMonitoring?: boolean;
})
```

**Parameters:**
- `options.cacheSize` (number, optional): Cache size. Default: 50
- `options.cacheTTL` (number, optional): Cache TTL in ms. Default: 3600000 (1 hour)
- `options.maxConcurrentAnalyses` (number, optional): Max concurrent analyses. Default: 5
- `options.enableRealTimeMonitoring` (boolean, optional): Enable monitoring. Default: true

#### Methods

##### analyzeDependencies()

```typescript
async analyzeDependencies(
  request: DependencyAnalysisRequest
): Promise<DependencyAnalysisResult>
```

Performs comprehensive dependency analysis.

**Parameters:**
- `request` (DependencyAnalysisRequest): Analysis request configuration

**Returns:** Promise\<DependencyAnalysisResult\>

**Example:**
```typescript
const result = await analyzer.analyzeDependencies({
  id: 'analysis-001',
  projectRoot: '/path/to/project',
  analysisScope: 'project',
  includeExternal: true,
  maxDepth: 5,
  analysisTypes: ['structural', 'circular', 'risk']
});

console.log(`Found ${result.circularDependencies.length} circular dependencies`);
console.log(`Overall risk: ${result.riskAssessment.overallRisk}`);
console.log(`Modularity score: ${result.metrics.modularityScore}`);
```

##### analyzeImpact()

```typescript
async analyzeImpact(request: ImpactAnalysisRequest): Promise<ImpactAnalysis>
```

Analyzes the impact of proposed changes.

**Parameters:**
- `request` (ImpactAnalysisRequest): Impact analysis request

**Returns:** Promise\<ImpactAnalysis\>

**Example:**
```typescript
const impact = await analyzer.analyzeImpact({
  id: 'impact-001',
  changes: [
    {
      type: 'modify',
      target: 'src/main.ts',
      description: 'Update main function',
      estimatedSize: 'medium'
    }
  ],
  analysisDepth: 'extended',
  includeRiskAssessment: true,
  testSuggestions: true
});
```

##### getExecution()

```typescript
getExecution(executionId: string): ValidationExecution | undefined
```

Gets the current execution status.

**Parameters:**
- `executionId` (string): Execution identifier

**Returns:** ValidationExecution | undefined

##### cancelExecution()

```typescript
async cancelExecution(executionId: string): Promise<boolean>
```

Cancels a running execution.

**Parameters:**
- `executionId` (string): Execution identifier

**Returns:** Promise\<boolean\> - true if successfully cancelled

#### Events

The Dependency Analyzer extends EventEmitter and emits:

- `analysisStarted`: Emitted when analysis starts
- `analysisCompleted`: Emitted when analysis completes
- `analysisError`: Emitted when analysis fails
- `cacheHit`: Emitted when cache is hit

**Event Data Examples:**
```typescript
analyzer.on('analysisStarted', (request: DependencyAnalysisRequest) => {
  console.log(`Analysis started: ${request.id}`);
});

analyzer.on('analysisCompleted', (data: { request: DependencyAnalysisRequest, result: DependencyAnalysisResult }) => {
  console.log(`Analysis completed: ${data.request.id}`);
  console.log(`Found ${data.result.nodes.length} nodes`);
});

analyzer.on('analysisError', (data: { request: DependencyAnalysisRequest, error: Error }) => {
  console.error(`Analysis failed: ${data.request.id}`, data.error);
});

analyzer.on('cacheHit', (data: { requestId: string, cached: DependencyAnalysisResult }) => {
  console.log(`Cache hit for: ${data.requestId}`);
});
```

---

## Event System API

### Event Emitter Pattern

All major components extend Node.js EventEmitter and follow consistent event naming patterns:

#### Event Naming Convention

- **Lifecycle Events**: `[action][State]` (e.g., `analysisStarted`, `stepCompleted`)
- **Error Events**: `[component]Error` (e.g., `analysisError`, `validationError`)
- **Data Events**: `[action]` (e.g., `cacheHit`, `planCreated`)

#### Event Handler Registration

```typescript
// Single event
component.on('eventName', (data) => { /* handle event */ });

// Multiple events
component.on('analysisStarted', handleStart);
component.on('analysisCompleted', handleComplete);
component.on('analysisError', handleError);

// One-time event
component.once('analysisCompleted', handleComplete);

// Remove event listener
component.removeListener('eventName', handler);
```

#### Event Data Structure

All events include consistent metadata:

```typescript
interface EventData {
  timestamp: Date;
  component: string;
  eventId: string;
  data: any;
  correlationId?: string;
}
```

---

## Configuration API

### System Configuration

```typescript
interface SystemConfig {
  // Performance settings
  performance: {
    maxConcurrentAnalyses: number;
    cacheSize: number;
    cacheTTL: number;
    defaultTimeout: number;
  };
  
  // Security settings
  security: {
    maxMemoryUsage: number;
    enableInputValidation: boolean;
    rateLimitWindow: number;
    rateLimitMax: number;
  };
  
  // Logging settings
  logging: {
    level: 'debug' | 'info' | 'warn' | 'error';
    enableMetrics: boolean;
    filePath?: string;
  };
}
```

### Configuration Loading

```typescript
import { loadConfig } from './config/loader.js';

// Load configuration
const config = await loadConfig();

// Initialize components with config
const analyzer = new DependencyAnalyzer(config.performance);
const engine = new SequentialInferenceEngine(config.performance);
```

---

## Error Handling

### Error Types

#### Base Error Classes

```typescript
class AEFrameworkError extends Error {
  constructor(
    message: string,
    public code: string,
    public details?: any
  ) {
    super(message);
    this.name = this.constructor.name;
  }
}

class ValidationError extends AEFrameworkError {
  constructor(message: string, details?: any) {
    super(message, 'VALIDATION_ERROR', details);
  }
}

class AnalysisError extends AEFrameworkError {
  constructor(message: string, details?: any) {
    super(message, 'ANALYSIS_ERROR', details);
  }
}

class InferenceError extends AEFrameworkError {
  constructor(message: string, details?: any) {
    super(message, 'INFERENCE_ERROR', details);
  }
}
```

#### Error Handling Patterns

```typescript
try {
  const result = await analyzer.analyzeDependencies(request);
  return result;
} catch (error) {
  if (error instanceof ValidationError) {
    // Handle validation errors
    console.error('Validation failed:', error.message);
    return { error: 'Invalid request', details: error.details };
  } else if (error instanceof AnalysisError) {
    // Handle analysis errors
    console.error('Analysis failed:', error.message);
    return { error: 'Analysis failed', retry: true };
  } else {
    // Handle unexpected errors
    console.error('Unexpected error:', error);
    throw error;
  }
}
```

### Retry Mechanisms

```typescript
// Automatic retry with exponential backoff
const retryConfig = {
  maxRetries: 3,
  baseDelay: 1000,
  maxDelay: 10000,
  backoffStrategy: 'exponential' as const
};

const result = await withRetry(
  () => analyzer.analyzeDependencies(request),
  retryConfig
);
```

---

## Type Definitions

### Core Types

#### ComplexQuery

```typescript
export interface ComplexQuery {
  id: string;
  description: string;
  context: Record<string, any>;
  priority: 'low' | 'medium' | 'high' | 'critical';
  constraints?: QueryConstraint[];
  expectedOutcome?: string;
}
```

#### Problem

```typescript
export interface Problem {
  id: string;
  title: string;
  description: string;
  domain: string;
  complexity: 'low' | 'medium' | 'high' | 'critical';
  priority: 'low' | 'medium' | 'high' | 'critical';
  constraints: Constraint[];
  context: Record<string, any>;
  expectedOutcome?: string;
  deadline?: Date;
}
```

#### DependencyAnalysisRequest

```typescript
export interface DependencyAnalysisRequest {
  id: string;
  projectRoot: string;
  targetFiles?: string[];
  analysisScope: 'project' | 'module' | 'file' | 'function';
  includeExternal: boolean;
  maxDepth?: number;
  excludePatterns?: string[];
  analysisTypes: DependencyAnalysisType[];
}

export type DependencyAnalysisType = 
  | 'structural'
  | 'functional' 
  | 'circular'
  | 'impact'
  | 'risk'
  | 'optimization'
  | 'security'
  | 'performance';
```

#### Results Types

```typescript
export interface DependencyAnalysisResult {
  requestId: string;
  graph: DependencyGraph;
  nodes: DependencyNode[];
  circularDependencies: CircularDependency[];
  metrics: DependencyMetrics;
  riskAssessment: DependencyRiskAssessment;
  recommendations: DependencyRecommendation[];
  impactAnalysis?: ImpactAnalysis;
  optimizationSuggestions: OptimizationSuggestion[];
}

export interface InferenceResult {
  queryId: string;
  steps: StepResult[];
  finalResult: any;
  confidence: number;
  executionTime: number;
  metadata: {
    stepsExecuted: number;
    cacheHits: number;
    errors: string[];
  };
}
```

---

## Usage Examples

### Complete Analysis Workflow

```typescript
import { 
  SequentialInferenceEngine,
  DependencyAnalyzer,
  ProblemDecomposer,
  ValidationOrchestrator 
} from '@ae-framework/phase3-1';

async function performCompleteAnalysis(projectPath: string) {
  // Initialize components
  const inferenceEngine = new SequentialInferenceEngine({
    maxSteps: 100,
    defaultTimeout: 30000,
    enableCaching: true
  });

  const dependencyAnalyzer = new DependencyAnalyzer({
    cacheSize: 50,
    cacheTTL: 3600000,
    maxConcurrentAnalyses: 3,
    enableRealTimeMonitoring: true
  });

  const problemDecomposer = new ProblemDecomposer();
  const validationOrchestrator = new ValidationOrchestrator();

  // Set up event listeners
  dependencyAnalyzer.on('analysisStarted', (request) => {
    console.log(`🔄 Analysis started: ${request.id}`);
  });

  dependencyAnalyzer.on('analysisCompleted', ({ result }) => {
    console.log(`✅ Analysis completed: ${result.requestId}`);
    console.log(`   - Nodes: ${result.nodes.length}`);
    console.log(`   - Circular Dependencies: ${result.circularDependencies.length}`);
    console.log(`   - Risk Level: ${result.riskAssessment.overallRisk}`);
  });

  try {
    // Step 1: Dependency Analysis
    const dependencyResult = await dependencyAnalyzer.analyzeDependencies({
      id: 'main-analysis',
      projectRoot: projectPath,
      analysisScope: 'project',
      includeExternal: true,
      maxDepth: 10,
      analysisTypes: ['structural', 'circular', 'risk', 'optimization']
    });

    // Step 2: Problem Decomposition
    if (dependencyResult.riskAssessment.overallRisk !== 'low') {
      const problem = {
        id: 'optimization-problem',
        title: 'System Optimization Required',
        description: `Address ${dependencyResult.circularDependencies.length} circular dependencies and ${dependencyResult.riskAssessment.riskFactors.length} risk factors`,
        domain: 'software_development',
        complexity: 'high' as const,
        priority: 'high' as const,
        constraints: [],
        context: {
          dependencyResult,
          projectPath
        }
      };

      const decomposition = await problemDecomposer.decompose(problem);
      console.log(`📋 Problem decomposed into ${decomposition.subProblems.length} sub-problems`);

      // Step 3: Validation Planning
      const validationPlan = await validationOrchestrator.createValidationPlan(
        dependencyResult,
        {
          originalProblem: problem,
          constraints: [],
          metadata: { projectPath }
        },
        {
          categories: ['structural', 'security', 'performance'],
          criticalityLevel: 'high'
        }
      );

      console.log(`🔍 Validation plan created with ${validationPlan.phases.length} phases`);

      // Step 4: Execute Validation
      const validationResult = await validationOrchestrator.executeValidationPlan(
        validationPlan.id,
        dependencyResult,
        {
          originalProblem: problem,
          constraints: [],
          metadata: { projectPath }
        }
      );

      console.log(`📊 Validation completed - Success: ${validationResult.overallResult.success}`);
    }

    // Step 5: Impact Analysis for Proposed Changes
    const impactResult = await dependencyAnalyzer.analyzeImpact({
      id: 'impact-analysis',
      changes: [
        {
          type: 'modify',
          target: 'src/main.ts',
          description: 'Refactor main module to break circular dependency',
          estimatedSize: 'large'
        }
      ],
      analysisDepth: 'comprehensive',
      includeRiskAssessment: true,
      testSuggestions: true
    });

    console.log(`🎯 Impact analysis: ${impactResult.affectedComponents.length} components affected`);

    return {
      dependencies: dependencyResult,
      impact: impactResult,
      summary: {
        totalNodes: dependencyResult.nodes.length,
        circularDependencies: dependencyResult.circularDependencies.length,
        riskLevel: dependencyResult.riskAssessment.overallRisk,
        recommendations: dependencyResult.recommendations.length,
        affectedByChanges: impactResult.affectedComponents.length
      }
    };

  } catch (error) {
    console.error('❌ Analysis failed:', error);
    throw error;
  }
}

// Usage
performCompleteAnalysis('/path/to/project')
  .then(result => {
    console.log('🎉 Complete analysis finished:', result.summary);
  })
  .catch(error => {
    console.error('💥 Analysis pipeline failed:', error.message);
  });
```

### Custom Strategy Registration

```typescript
// Register custom decomposition strategy
problemDecomposer.registerDecompositionStrategy('data_science', (problem) => {
  return [
    {
      id: `${problem.id}-data-collection`,
      parentId: problem.id,
      title: 'Data Collection',
      description: 'Gather and validate data sources',
      type: 'sequential',
      dependencies: [],
      estimatedComplexity: 3,
      estimatedTime: 2,
      requiredResources: ['data_engineer'],
      constraints: [],
      successCriteria: ['Data validated', 'Quality assured'],
      fallbackStrategies: ['Use synthetic data', 'Sample dataset']
    },
    {
      id: `${problem.id}-analysis`,
      parentId: problem.id,
      title: 'Data Analysis',
      description: 'Perform statistical analysis',
      type: 'parallel',
      dependencies: [`${problem.id}-data-collection`],
      estimatedComplexity: 5,
      estimatedTime: 4,
      requiredResources: ['data_scientist', 'analysis_tools'],
      constraints: [],
      successCriteria: ['Analysis complete', 'Results validated'],
      fallbackStrategies: ['Simplified analysis', 'Manual review']
    }
  ];
});

// Register custom validator
validationOrchestrator.registerValidator({
  id: 'custom-performance-validator',
  category: 'performance',
  validate: async (target, context, config) => {
    // Custom validation logic
    const performanceScore = calculatePerformanceScore(target);
    
    return {
      criterion: 'custom_performance',
      passed: performanceScore > 0.8,
      score: performanceScore,
      details: `Performance score: ${performanceScore}`,
      importance: 'high'
    };
  },
  canHandle: (target, context) => {
    return context.metadata.includePerformance === true;
  }
});
```

### Monitoring and Metrics

```typescript
// Set up comprehensive monitoring
function setupMonitoring(components: {
  analyzer: DependencyAnalyzer;
  engine: SequentialInferenceEngine;
  orchestrator: ValidationOrchestrator;
}) {
  const metrics = {
    analysesStarted: 0,
    analysesCompleted: 0,
    analysesErrored: 0,
    totalExecutionTime: 0,
    cacheHits: 0
  };

  // Dependency Analyzer metrics
  components.analyzer.on('analysisStarted', () => {
    metrics.analysesStarted++;
    console.log(`📊 Metrics - Analyses started: ${metrics.analysesStarted}`);
  });

  components.analyzer.on('analysisCompleted', ({ result }) => {
    metrics.analysesCompleted++;
    console.log(`📊 Metrics - Analyses completed: ${metrics.analysesCompleted}`);
  });

  components.analyzer.on('analysisError', () => {
    metrics.analysesErrored++;
    console.log(`📊 Metrics - Analyses errored: ${metrics.analysesErrored}`);
  });

  components.analyzer.on('cacheHit', () => {
    metrics.cacheHits++;
    console.log(`📊 Metrics - Cache hits: ${metrics.cacheHits}`);
  });

  // Inference Engine metrics
  components.engine.on('stepCompleted', (data) => {
    metrics.totalExecutionTime += data.executionTime || 0;
  });

  // Health check endpoint
  const getHealthStatus = () => ({
    status: 'healthy',
    uptime: process.uptime(),
    metrics: {
      ...metrics,
      successRate: metrics.analysesCompleted / (metrics.analysesStarted || 1),
      averageExecutionTime: metrics.totalExecutionTime / (metrics.analysesCompleted || 1),
      cacheHitRate: metrics.cacheHits / (metrics.analysesCompleted || 1)
    },
    timestamp: new Date().toISOString()
  });

  return { getHealthStatus, metrics };
}
```

---

This API reference provides comprehensive documentation for all Phase 3.1 components. For additional examples and advanced usage patterns, refer to the test files in the `tests/` directory and the detailed design documentation.

**API Version**: 3.1.0  
**Last Updated**: 2025-08-13  
**Compatibility**: Node.js 18+, TypeScript 5.0+
