# Circuit Breaker Pattern Implementation

The Circuit Breaker pattern implementation provides fault tolerance and resilience for the AE-Framework by preventing cascading failures and providing graceful degradation when services become unavailable.

## Overview

The Circuit Breaker pattern acts as a protective wrapper around potentially unreliable operations, monitoring their failure rate and automatically switching to a fallback mechanism when failures exceed a configured threshold.

### States

- **CLOSED**: Normal operation, requests pass through
- **OPEN**: Failing fast, rejecting requests immediately
- **HALF_OPEN**: Testing if service has recovered

### Key Features

- **Configurable thresholds**: Failure and success thresholds
- **Timeout handling**: Automatic retry after timeout period
- **Fallback mechanisms**: Graceful degradation when circuit is open
- **Monitoring and metrics**: Comprehensive statistics and health reporting
- **Event-driven architecture**: Real-time notifications and integration
- **AE-Framework integration**: Specialized support for framework components

## Architecture

```typescript
┌─────────────────────┐    ┌─────────────────────┐    ┌─────────────────────┐
│  Application Code   │───▶│   Circuit Breaker   │───▶│  Protected Service  │
├─────────────────────┤    ├─────────────────────┤    ├─────────────────────┤
│ - Agent Operations  │    │ - State Management  │    │ - External APIs     │
│ - State Management  │    │ - Failure Detection │    │ - Database Access   │
│ - Phase Transitions │    │ - Fallback Handling │    │ - File Operations   │
│ - External Calls    │    │ - Metrics Tracking  │    │ - Resource Access   │
└─────────────────────┘    └─────────────────────┘    └─────────────────────┘
                                      │
                                      ▼
                           ┌─────────────────────┐
                           │   Fallback Logic    │
                           ├─────────────────────┤
                           │ - Cached Responses  │
                           │ - Default Values    │
                           │ - Alternative APIs  │
                           │ - Error Messages    │
                           └─────────────────────┘
```

## Basic Usage

### Creating a Circuit Breaker

```typescript
import { CircuitBreaker } from '../utils/circuit-breaker.js';

const breaker = new CircuitBreaker('api-service', {
  failureThreshold: 5,      // Open after 5 failures
  successThreshold: 3,      // Close after 3 successes in half-open
  timeout: 60000,          // 60 second timeout before half-open
  monitoringWindow: 60000, // 60 second monitoring window
  enableMonitoring: true   // Enable detailed metrics
});
```

### Executing Operations

```typescript
// Async operation
const result = await breaker.execute(async () => {
  const response = await fetch('https://api.example.com/data');
  return response.json();
});

// Sync operation
const result = breaker.executeSync(() => {
  return expensiveCalculation();
});
```

### With Fallback

```typescript
const breaker = new CircuitBreaker('api-service', {
  failureThreshold: 3,
  fallback: () => ({
    data: [],
    cached: true,
    timestamp: new Date().toISOString()
  })
});
```

## AE-Framework Integration

### Pre-configured Circuit Breakers

The framework provides pre-configured circuit breakers for common scenarios:

```typescript
import { aeFrameworkCircuitBreakers } from '../integration/circuit-breaker-integration.js';

// Agent communication
const agentBreaker = aeFrameworkCircuitBreakers.getAgentCircuitBreaker('intent-agent');

// State management
const stateBreaker = aeFrameworkCircuitBreakers.getStateManagementCircuitBreaker();

// Phase transitions
const phaseBreaker = aeFrameworkCircuitBreakers.getPhaseTransitionCircuitBreaker();

// External services
const serviceBreaker = aeFrameworkCircuitBreakers.getExternalServiceCircuitBreaker('github-api');

// Resource operations
const resourceBreaker = aeFrameworkCircuitBreakers.getResourceCircuitBreaker('file-system');
```

### High-level Execution Methods

```typescript
// Execute agent operation with protection
const agentResult = await aeFrameworkCircuitBreakers.executeAgentOperation(
  'intent-agent',
  async () => {
    return await intentAgent.processUserInput(input);
  },
  { userId: 'user123', operation: 'process_intent' }
);

// Execute state management operation
const stateResult = await aeFrameworkCircuitBreakers.executeStateOperation(
  'save_specification',
  async () => {
    return await stateManager.saveSpecification(spec);
  },
  { specId: 'spec456', phase: 'phase-5' }
);

// Execute phase transition
const transitionResult = await aeFrameworkCircuitBreakers.executePhaseTransition(
  'phase-4',
  'phase-5',
  async () => {
    return await phaseManager.transition('phase-4', 'phase-5');
  },
  { userId: 'user123', projectId: 'proj789' }
);
```

### Decorator Pattern

```typescript
import { WithCircuitBreaker } from '../integration/circuit-breaker-integration.js';

class ApiService {
  @WithCircuitBreaker('external-api', {
    failureThreshold: 3,
    timeout: 30000,
    fallback: () => ({ error: 'Service temporarily unavailable' })
  })
  async fetchData(id: string): Promise<any> {
    const response = await fetch(`https://api.example.com/data/${id}`);
    return response.json();
  }
}
```

## CLI Interface

### Basic Commands

```bash
# Create a circuit breaker
ae-framework circuit-breaker create -n "api-service" -f 5 -s 3 -t 60000

# List all circuit breakers
ae-framework circuit-breaker list

# Show detailed statistics
ae-framework circuit-breaker stats -n "api-service"

# Generate health report
ae-framework circuit-breaker health

# Test circuit breaker with simulated load
ae-framework circuit-breaker test -n "api-service" -o 50 -f 0.3 -d 100

# Watch real-time state changes
ae-framework circuit-breaker watch

# Reset circuit breaker
ae-framework circuit-breaker reset -n "api-service"

# Force states (for testing)
ae-framework circuit-breaker force-open -n "api-service"
ae-framework circuit-breaker force-close -n "api-service"
```

### NPM Scripts

```bash
# Create circuit breaker
npm run circuit-breaker:create -- -n "my-service" -f 5

# List all circuit breakers
npm run circuit-breaker:list

# Show statistics
npm run circuit-breaker:stats -- -n "my-service"

# Health report
npm run circuit-breaker:health

# Test circuit breaker
npm run circuit-breaker:test -- -n "my-service" -o 20 -f 0.4

# Watch state changes
npm run circuit-breaker:watch

# Reset circuit breaker
npm run circuit-breaker:reset -- -n "my-service"
```

## Configuration Options

```typescript
interface CircuitBreakerOptions {
  /** Failure threshold to open circuit (default: 5) */
  failureThreshold: number;
  
  /** Success threshold to close circuit from half-open (default: 3) */
  successThreshold: number;
  
  /** Timeout before attempting to half-open (ms, default: 60000) */
  timeout: number;
  
  /** Monitor window for failures (ms, default: 60000) */
  monitoringWindow: number;
  
  /** Expected error types that should trigger circuit breaking */
  expectedErrors?: Array<new (...args: any[]) => Error>;
  
  /** Fallback function when circuit is open */
  fallback?: (...args: any[]) => any;
  
  /** Enable detailed monitoring and metrics */
  enableMonitoring?: boolean;
}
```

### Framework-specific Defaults

```typescript
// Agent communication
{
  failureThreshold: 5,
  successThreshold: 3,
  timeout: 30000,
  expectedErrors: [AgentCommunicationError, ExternalServiceError]
}

// State management
{
  failureThreshold: 3,
  successThreshold: 2,
  timeout: 15000,
  expectedErrors: [StateManagementError]
}

// Phase transitions
{
  failureThreshold: 2,
  successThreshold: 1,
  timeout: 60000,
  expectedErrors: [PhaseTransitionError, StateManagementError]
}

// External services
{
  failureThreshold: 3,
  successThreshold: 2,
  timeout: 20000,
  expectedErrors: [ExternalServiceError]
}

// Resource operations
{
  failureThreshold: 2,
  successThreshold: 1,
  timeout: 45000,
  expectedErrors: [ResourceExhaustionError]
}
```

## Monitoring and Metrics

### Statistics

```typescript
interface CircuitBreakerStats {
  state: CircuitState;
  failureCount: number;
  successCount: number;
  lastFailureTime: number | null;
  lastSuccessTime: number | null;
  totalRequests: number;
  totalFailures: number;
  totalSuccesses: number;
  circuitOpenCount: number;
  averageResponseTime: number;
  uptime: number;
}

const stats = breaker.getStats();
console.log('Circuit Breaker Statistics:', stats);
```

### Health Reporting

```typescript
const healthReport = breaker.generateHealthReport();
console.log('Health Report:', {
  name: healthReport.name,
  state: healthReport.state,
  health: healthReport.health, // 'healthy' | 'degraded' | 'unhealthy'
  recentFailures: healthReport.recentFailures,
  recommendations: healthReport.recommendations
});
```

### Framework Health Status

```typescript
const frameworkHealth = aeFrameworkCircuitBreakers.getFrameworkHealthStatus();
console.log('Framework Health:', {
  overall: frameworkHealth.overall, // 'healthy' | 'degraded' | 'critical'
  components: frameworkHealth.components,
  recommendations: frameworkHealth.recommendations
});
```

## Event System

### Circuit Breaker Events

```typescript
breaker.on('circuitOpened', (event) => {
  console.log(`Circuit opened: ${event.name} after ${event.failureCount} failures`);
});

breaker.on('circuitClosed', (event) => {
  console.log(`Circuit closed: ${event.name} after ${event.successCount} successes`);
});

breaker.on('stateChanged', (event) => {
  console.log(`State changed: ${event.name} ${event.previousState} → ${event.newState}`);
});

breaker.on('operationSuccess', (event) => {
  console.log(`Operation succeeded: ${event.name} in ${event.duration}ms`);
});

breaker.on('operationFailure', (event) => {
  console.log(`Operation failed: ${event.name} - ${event.error.message}`);
});

breaker.on('callRejected', (event) => {
  console.log(`Call rejected: ${event.name} - ${event.reason}`);
});
```

### Framework Integration Events

```typescript
aeFrameworkCircuitBreakers.on('agentOperationFailed', (event) => {
  console.log(`Agent operation failed: ${event.agentName}`, event.error);
});

aeFrameworkCircuitBreakers.on('stateOperationFailed', (event) => {
  console.log(`State operation failed: ${event.operationType}`, event.error);
});

aeFrameworkCircuitBreakers.on('phaseTransitionFailed', (event) => {
  console.log(`Phase transition failed: ${event.fromPhase} → ${event.toPhase}`, event.error);
});

aeFrameworkCircuitBreakers.on('circuitBreakerOpened', (event) => {
  console.error(`🚨 Circuit breaker opened: ${event.name}`);
});
```

## Advanced Patterns

### Retry with Circuit Breaker

```typescript
import { CircuitBreakerUtils } from '../integration/circuit-breaker-integration.js';

const result = await CircuitBreakerUtils.executeWithRetryAndCircuitBreaker(
  async () => {
    return await unreliableOperation();
  },
  breaker,
  {
    maxRetries: 3,
    delayMs: 1000,
    backoffMultiplier: 2
  }
);
```

### Timeout with Circuit Breaker

```typescript
const result = await CircuitBreakerUtils.executeWithTimeoutAndCircuitBreaker(
  async () => {
    return await slowOperation();
  },
  breaker,
  5000 // 5 second timeout
);
```

### Bulk Operations

```typescript
const results = await CircuitBreakerUtils.executeBulkWithCircuitBreaker(
  items,
  async (item) => {
    return await processItem(item);
  },
  breaker,
  {
    concurrency: 5,
    failFast: false
  }
);
```

## Error Types

### Framework-specific Errors

```typescript
import {
  AgentCommunicationError,
  StateManagementError,
  PhaseTransitionError,
  ExternalServiceError,
  ResourceExhaustionError
} from '../integration/circuit-breaker-integration.js';

// Use specific error types for better circuit breaker filtering
throw new AgentCommunicationError('Failed to communicate with intent agent');
throw new StateManagementError('Failed to save specification state');
throw new PhaseTransitionError('Cannot transition from phase-3 to phase-5');
throw new ExternalServiceError('GitHub API rate limit exceeded');
throw new ResourceExhaustionError('Insufficient memory for large specification processing');
```

### Error Filtering

```typescript
const breaker = new CircuitBreaker('selective-breaker', {
  failureThreshold: 3,
  expectedErrors: [ExternalServiceError, ResourceExhaustionError],
  // Only these error types will count towards failure threshold
  // Other errors pass through but don't affect circuit state
});
```

## Best Practices

### 1. Choose Appropriate Thresholds

```typescript
// For critical services - fail fast
const criticalBreaker = new CircuitBreaker('critical-service', {
  failureThreshold: 2,
  timeout: 30000
});

// For non-critical services - more tolerant
const optionalBreaker = new CircuitBreaker('optional-service', {
  failureThreshold: 10,
  timeout: 120000
});
```

### 2. Implement Meaningful Fallbacks

```typescript
const userServiceBreaker = new CircuitBreaker('user-service', {
  fallback: (userId) => ({
    id: userId,
    name: 'Unknown User',
    email: 'unknown@example.com',
    cached: true,
    source: 'fallback'
  })
});

const recommendationBreaker = new CircuitBreaker('recommendation-service', {
  fallback: () => ({
    recommendations: [],
    message: 'Recommendations temporarily unavailable',
    fallback: true
  })
});
```

### 3. Monitor and Alert

```typescript
// Set up monitoring for critical circuit breakers
circuitBreakerManager.on('circuitOpened', (event) => {
  if (event.name.includes('critical')) {
    // Send alert to operations team
    alertingService.sendAlert({
      severity: 'high',
      message: `Critical circuit breaker opened: ${event.name}`,
      context: event
    });
  }
});

// Health check endpoint
app.get('/health/circuit-breakers', (req, res) => {
  const health = aeFrameworkCircuitBreakers.getFrameworkHealthStatus();
  
  const status = health.overall === 'critical' ? 503 : 
                 health.overall === 'degraded' ? 200 : 200;
  
  res.status(status).json(health);
});
```

### 4. Testing Circuit Breakers

```typescript
// Unit tests
describe('Circuit Breaker Integration', () => {
  it('should protect agent operations', async () => {
    const breaker = aeFrameworkCircuitBreakers.getAgentCircuitBreaker('test-agent');
    
    // Simulate failures
    const failingOperation = jest.fn().mockRejectedValue(new AgentCommunicationError('Connection failed'));
    
    // Should fail initially
    await expect(breaker.execute(failingOperation)).rejects.toThrow();
    await expect(breaker.execute(failingOperation)).rejects.toThrow();
    await expect(breaker.execute(failingOperation)).rejects.toThrow();
    
    // Circuit should be open now
    expect(breaker.getState()).toBe(CircuitState.OPEN);
    
    // Further calls should be rejected immediately
    await expect(breaker.execute(failingOperation)).rejects.toThrow(CircuitBreakerOpenError);
    expect(failingOperation).toHaveBeenCalledTimes(3); // No additional calls
  });
});

// Integration tests
describe('End-to-End Circuit Breaker', () => {
  it('should handle complete failure and recovery cycle', async () => {
    // Test full lifecycle: closed → open → half-open → closed
  });
});
```

### 5. Gradual Rollout

```typescript
// Feature flag integration
const shouldUseCircuitBreaker = featureFlags.isEnabled('circuit-breaker-rollout');

const executeWithOptionalProtection = async (operation) => {
  if (shouldUseCircuitBreaker) {
    return await breaker.execute(operation);
  } else {
    return await operation();
  }
};
```

## Troubleshooting

### Common Issues

1. **Circuit opens too frequently**
   - Increase `failureThreshold`
   - Increase `monitoringWindow`
   - Check if errors are actually indicative of service health

2. **Circuit stays open too long**
   - Decrease `timeout`
   - Ensure service recovery is detectable
   - Check success threshold requirements

3. **Fallbacks not working**
   - Verify fallback function is provided and correct
   - Check for exceptions in fallback logic
   - Ensure fallback returns expected data structure

4. **Performance impact**
   - Disable monitoring for high-throughput operations
   - Increase monitoring window to reduce memory usage
   - Use synchronous operations where possible

### Debugging

```typescript
// Enable debug logging
breaker.on('operationSuccess', (event) => {
  console.debug(`✅ ${event.name}: ${event.duration}ms`);
});

breaker.on('operationFailure', (event) => {
  console.debug(`❌ ${event.name}: ${event.error.message} (${event.duration}ms)`);
});

breaker.on('stateChanged', (event) => {
  console.debug(`🔄 ${event.name}: ${event.previousState} → ${event.newState}`);
});

// Inspect circuit breaker state
console.log('Current state:', breaker.getState());
console.log('Statistics:', breaker.getStats());
console.log('Health report:', breaker.generateHealthReport());
```

## Performance Considerations

### Memory Usage

- Circuit breakers store request history for monitoring
- History is automatically cleaned up based on `monitoringWindow`
- Disable monitoring for high-frequency, low-impact operations

### CPU Overhead

- Minimal overhead for successful operations
- Failure detection and state transitions are lightweight
- Event emission can be disabled if not needed

### Network Impact

- Circuit breakers prevent unnecessary network calls when open
- Fallbacks should be fast and local when possible
- Consider caching strategies in fallback implementations

## Integration with Other Framework Components

### State Management

```typescript
// Protect state operations with circuit breakers
const enhancedStateManager = {
  async saveSSOT(key, data) {
    return aeFrameworkCircuitBreakers.executeStateOperation(
      'save_ssot',
      () => stateManager.saveSSOT(key, data)
    );
  }
};
```

### Agent Communication

```typescript
// Protect agent interactions
const protectedAgent = {
  async processIntent(input) {
    return aeFrameworkCircuitBreakers.executeAgentOperation(
      'intent-agent',
      () => intentAgent.process(input)
    );
  }
};
```

### External APIs

```typescript
// Protect external service calls
const githubApi = {
  async getRepository(owner, repo) {
    return aeFrameworkCircuitBreakers.executeExternalServiceCall(
      'github-api',
      () => octokit.rest.repos.get({ owner, repo })
    );
  }
};
```

This Circuit Breaker implementation provides comprehensive fault tolerance for the AE-Framework, ensuring system resilience and graceful degradation under failure conditions while maintaining visibility into system health and performance.