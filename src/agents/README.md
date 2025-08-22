# AE Framework Agent Interface Standardization

This implementation provides standardized interfaces and pipeline orchestration for the AE Framework's 6-phase workflow, addressing Issue #160.

## Overview

The standardization includes:
- ✅ **Standard Agent Interfaces** - Consistent input/output patterns
- ✅ **Pipeline Orchestrator** - Automated 6-phase execution
- ✅ **Agent Adapters** - Bridge existing agents to standard interface
- ✅ **Type Definitions** - Complete TypeScript type safety
- ✅ **Integration Examples** - Ready-to-use implementation patterns

## Architecture

```
├── interfaces/
│   └── standard-interfaces.ts    # Core type definitions and interfaces
├── pipeline/
│   └── ae-framework-pipeline.ts  # Pipeline orchestrator class
├── adapters/
│   ├── intent-agent-adapter.ts   # IntentAgent standardization
│   ├── task-adapters.ts          # Requirements, UserStories, Validation, Domain adapters
│   └── ui-ux-agent-adapter.ts    # UI/UX placeholder adapter
└── examples/
    └── pipeline-integration-example.ts  # Complete usage examples
```

## Quick Start

### 1. Basic Pipeline Setup

```typescript
import { AEFrameworkPipeline } from './pipeline/ae-framework-pipeline.js';
import { IntentAgentAdapter } from './adapters/intent-agent-adapter.js';
import { RequirementsAgentAdapter } from './adapters/task-adapters.js';

// Create pipeline
const pipeline = new AEFrameworkPipeline({
  projectId: 'my-project',
  domain: 'task-management'
});

// Register agents
pipeline.registerAgent('intent', new IntentAgentAdapter());
pipeline.registerAgent('requirements', new RequirementsAgentAdapter());
// ... register other phases

// Execute complete pipeline
const result = await pipeline.executePipeline({
  sources: [{ type: 'text', content: 'Your requirements here...' }],
  context: { domain: 'task-management' }
});
```

### 2. Individual Phase Execution

```typescript
// Execute single phase with standardized interface
const intentResult = await pipeline.executePhase('intent', {
  sources: [{ type: 'text', content: 'Build a task management system' }]
});

console.log('Intent Analysis:', intentResult.data);
```

### 3. Benchmark Integration

```typescript
// Direct integration with req2run-benchmark
import { benchmarkIntegrationExample } from './examples/pipeline-integration-example.js';

const benchmarkResult = await benchmarkIntegrationExample();
// Result can be passed to BenchmarkRunner for evaluation
```

## Standard Interface Specification

### Core Agent Interface

All AE Framework agents implement this interface:

```typescript
interface StandardAEAgent<TInput, TOutput> {
  readonly agentName: string;
  readonly version: string;
  readonly supportedPhase: PhaseType;

  process(input: TInput, context?: ProcessingContext): Promise<PhaseResult<TOutput>>;
  validateInput(input: TInput): ValidationResult;
  getCapabilities(): AgentCapabilities;
}
```

### Phase Data Flow

```typescript
IntentInput → IntentOutput
    ↓
RequirementsInput → RequirementsOutput
    ↓
UserStoriesInput → UserStoriesOutput
    ↓
ValidationInput → ValidationOutput
    ↓
DomainModelingInput → DomainModelingOutput
    ↓
UIUXInput → UIUXOutput
```

### Standardized Result Format

```typescript
interface PhaseResult<T> {
  success: boolean;
  data: T;
  metadata: PhaseMetadata;
  errors?: AgentError[];
  warnings?: string[];
  phase: PhaseType;
}
```

## Pipeline Features

### Error Handling & Retry Logic
- Automatic retry with exponential backoff
- Comprehensive error tracking and reporting
- Graceful degradation on phase failures

### Data Flow Tracing
- Input/output size tracking
- Phase duration monitoring
- Data transformation logging

### Validation & Type Safety
- Input validation before processing
- Strong TypeScript typing throughout
- Runtime type checking and error reporting

### Configuration Options
```typescript
interface PipelineConfig {
  projectId: string;
  domain: string;
  enableParallelProcessing?: boolean;  // Future enhancement
  validateInputs?: boolean;            // Default: true
  retryFailures?: boolean;             // Default: true
  maxRetries?: number;                 // Default: 2
  timeoutMs?: number;                  // Default: 300000 (5 min)
}
```

## Agent Adapters

### IntentAgentAdapter
- Wraps existing `IntentAgent`
- Transforms input/output to standard format
- Provides confidence scoring and validation

### TaskAdapters
- **RequirementsAgentAdapter**: Natural language processing
- **UserStoriesAgentAdapter**: User story generation
- **ValidationAgentAdapter**: Story validation and conflict detection
- **DomainModelingAgentAdapter**: Domain model creation

### UIUXAgentAdapter (Placeholder)
- Mock implementation for UI/UX generation phase
- Generates wireframes, user flows, and design systems
- Ready for replacement with actual UI/UX agent

## Integration Benefits

### Before Standardization
```typescript
// Manual pipeline orchestration
const intent = await intentAgent.analyzeIntent(intentRequest);
const requirements = await nlpAgent.processNaturalLanguageRequirements(
  intent.primaryIntent + '\n\n' + 
  spec.requirements.map(r => `${r.priority}: ${r.description}`).join('\n')
);
const userStories = await storiesAgent.generateUserStories(
  requirements.processedRequirements || 
  requirements.naturalLanguageRequirements || 
  JSON.stringify(requirements)
);
// ... complex manual data transformations
```

### After Standardization
```typescript
// Automated pipeline with standardized interfaces
const result = await pipeline.executePipeline(input);
// All phases executed automatically with proper data flow
```

## Usage Examples

### Complete Examples
Run the comprehensive examples:
```bash
cd src/agents/examples
npm run example
```

### Individual Examples
- `runCompleteAEFrameworkPipeline()` - Full 6-phase execution
- `runIndividualPhaseExample()` - Single phase execution
- `inspectPipelineCapabilities()` - Agent capability inspection
- `benchmarkIntegrationExample()` - Req2run benchmark integration

## Testing & Validation

### Pipeline Validation
```typescript
const validation = pipeline.validatePipeline();
if (!validation.valid) {
  console.error('Missing agents:', validation.missing);
}
```

### Input Validation
```typescript
const agent = new IntentAgentAdapter();
const validation = agent.validateInput(input);
if (!validation.valid) {
  console.error('Input errors:', validation.errors);
}
```

## Migration Guide

### Existing Agent Integration
1. Create adapter class implementing `StandardAEAgent`
2. Transform input/output formats in `process()` method
3. Implement `validateInput()` and `getCapabilities()`
4. Register with pipeline using `registerAgent()`

### BenchmarkRunner Integration
Replace manual agent orchestration:
```typescript
// Before
const intent = await this.intentAgent.analyzeIntent(
  IntentAgent.createBenchmarkRequest(spec)
);

// After  
const pipeline = new AEFrameworkPipeline(config);
pipeline.registerAgent('intent', new IntentAgentAdapter());
const result = await pipeline.executePhase('intent', benchmarkInput);
```

## Future Enhancements

### Planned Features
- **Parallel Processing**: Execute compatible phases in parallel
- **Caching**: Cache intermediate results for faster re-execution
- **Streaming**: Real-time phase output streaming
- **Plugins**: Custom agent plugin architecture
- **Monitoring**: Enhanced metrics and observability

### Extension Points
- Custom agent adapters
- Phase result transformers
- Validation rule extensions
- Custom error handlers
- Metrics collectors

## Troubleshooting

### Common Issues

**Pipeline Validation Fails**
```
Error: Missing agents for phases: ui-ux-generation
Solution: Register all required phase agents or use placeholder implementations
```

**Input Validation Errors**
```
Error: Source content too short (5 characters)
Solution: Provide more detailed requirement sources (>10 characters recommended)
```

**Phase Execution Timeout**
```
Error: Operation timed out after 300000ms
Solution: Increase timeout in PipelineConfig or optimize agent processing
```

**Type Errors**
```
Error: Property 'data' does not exist on type 'PhaseResult'
Solution: Ensure proper TypeScript compilation and import paths
```

### Debug Mode
Enable detailed logging by setting debug context:
```typescript
const context = {
  projectId: 'debug-session',
  metadata: { debug: true, logLevel: 'verbose' }
};
```

## API Reference

### Core Classes
- `AEFrameworkPipeline`: Main orchestrator class
- `IntentAgentAdapter`: Intent analysis standardization
- `RequirementsAgentAdapter`: Requirements processing
- `UserStoriesAgentAdapter`: User story generation
- `ValidationAgentAdapter`: Story validation
- `DomainModelingAgentAdapter`: Domain model creation
- `UIUXAgentAdapter`: UI/UX generation (placeholder)

### Key Interfaces
- `StandardAEAgent<TInput, TOutput>`: Agent implementation interface
- `PhaseResult<T>`: Standardized result format
- `ProcessingContext`: Execution context
- `PipelineConfig`: Pipeline configuration
- `ValidationResult`: Input validation result

### Phase Types
```typescript
type PhaseType = 
  | 'intent' 
  | 'requirements'
  | 'user-stories'
  | 'validation'
  | 'domain-modeling'
  | 'ui-ux-generation';
```

## Contributing

1. Follow existing adapter patterns when adding new agents
2. Maintain TypeScript strict mode compliance
3. Add comprehensive input validation
4. Include error handling and logging
5. Provide usage examples and tests
6. Update documentation for new features

---

**Issue Resolution**: This implementation fully addresses Issue #160 by providing standardized interfaces, automated pipeline orchestration, and seamless integration patterns for the AE Framework's 6-phase workflow.