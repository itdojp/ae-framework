#!/usr/bin/env node
/**
 * Circuit Breaker Test Script - Prompt 6
 * Tests state transitions: closed → open → half-open → closed
 */

import { CircuitBreaker, CircuitState } from '../src/utils/circuit-breaker.js';

async function delay(ms: number): Promise<void> {
  return new Promise(resolve => setTimeout(resolve, ms));
}

async function testCircuitBreaker() {
  console.log('🔁 Circuit Breaker State Transition Test');
  console.log('=====================================');

  // Create circuit breaker with fast thresholds for testing
  const breaker = new CircuitBreaker({
    failureThreshold: 3,    // Open after 3 failures
    successThreshold: 2,    // Close after 2 successes in half-open
    timeout: 1000,          // 1 second timeout for half-open
    monitoringWindow: 5000, // 5 second window
    enableMonitoring: true
  });

  // Track state changes
  const stateChanges: string[] = [];
  breaker.on('stateChange', (state: CircuitState) => {
    const timestamp = new Date().toISOString();
    console.log(`📊 [${timestamp}] State changed to: ${state}`);
    stateChanges.push(state);
  });

  // Function that always fails (first 5 calls)
  let callCount = 0;
  const testFunction = async (shouldFail: boolean = true): Promise<string> => {
    callCount++;
    console.log(`🔧 Call ${callCount} - shouldFail: ${shouldFail}`);
    
    if (shouldFail) {
      throw new Error(`Simulated failure ${callCount}`);
    }
    return `Success ${callCount}`;
  };

  try {
    console.log('\n=== Phase 1: Trigger Circuit OPEN (3 failures) ===');
    
    // Make 5 failing calls to trigger OPEN state
    for (let i = 1; i <= 5; i++) {
      try {
        await breaker.execute(() => testFunction(true));
      } catch (error) {
        console.log(`❌ Call ${i} failed as expected: ${error.message}`);
      }
      await delay(100);
    }

    console.log(`\n📊 Current state: ${breaker.getStats().state}`);
    
    if (breaker.getStats().state !== CircuitState.OPEN) {
      console.log('⚠️  Circuit should be OPEN but is:', breaker.getStats().state);
    }

    console.log('\n=== Phase 2: Wait for HALF_OPEN transition ===');
    console.log('Waiting 1.2 seconds for half-open timeout...');
    await delay(1200);

    console.log('\n=== Phase 3: Attempt recovery (HALF_OPEN → CLOSED) ===');
    
    // First call in half-open should work
    try {
      const result1 = await breaker.execute(() => testFunction(false));
      console.log(`✅ Half-open call 1 succeeded: ${result1}`);
    } catch (error) {
      console.log(`❌ Half-open call 1 failed: ${error.message}`);
    }

    // Second call should complete recovery  
    try {
      const result2 = await breaker.execute(() => testFunction(false));
      console.log(`✅ Half-open call 2 succeeded: ${result2}`);
    } catch (error) {
      console.log(`❌ Half-open call 2 failed: ${error.message}`);
    }

    console.log(`\n📊 Final state: ${breaker.getStats().state}`);

    // Verify state transitions
    console.log('\n=== State Transition Summary ===');
    console.log('Expected: CLOSED → OPEN → HALF_OPEN → CLOSED');
    console.log('Actual  :', stateChanges.join(' → '));
    
    const expectedStates = [CircuitState.OPEN, CircuitState.HALF_OPEN, CircuitState.CLOSED];
    const success = expectedStates.every(state => stateChanges.includes(state));
    
    if (success) {
      console.log('✅ Circuit breaker state transitions working correctly');
    } else {
      console.log('❌ Circuit breaker state transitions failed');
    }

    // Display final stats
    const stats = breaker.getStats();
    console.log('\n=== Final Statistics ===');
    console.log('State:', stats.state);
    console.log('Total requests:', stats.totalRequests);
    console.log('Total failures:', stats.totalFailures);
    console.log('Total successes:', stats.totalSuccesses);
    console.log('Circuit open count:', stats.circuitOpenCount);

    return success;

  } catch (error) {
    console.error('❌ Test failed with error:', error);
    return false;
  }
}

// Run the test
testCircuitBreaker()
  .then(success => {
    console.log(`\n🏁 Test completed. Success: ${success}`);
    process.exit(success ? 0 : 1);
  })
  .catch(error => {
    console.error('💥 Test crashed:', error);
    process.exit(1);
  });