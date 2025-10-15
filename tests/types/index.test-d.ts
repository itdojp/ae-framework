import { expectType } from 'tsd';
import { AEFrameworkCLI } from '../../src/cli/index.js';
import { CircuitBreaker } from '../../src/utils/circuit-breaker.js';
import { loadQualityPolicy } from '../../src/utils/quality-policy-loader.js';
import type { QualityPolicy } from '../../src/utils/quality-policy-loader.js';

// Test CLI types
const cli = new AEFrameworkCLI();
expectType<AEFrameworkCLI>(cli);

// Test Circuit Breaker types
const breaker = new CircuitBreaker('test', {
  failureThreshold: 3,
  successThreshold: 2,
  timeout: 1000,
  monitoringWindow: 5000,
  enableMonitoring: true
});
expectType<CircuitBreaker>(breaker);

const breakerWithFallback = new CircuitBreaker('test-fallback', {
  failureThreshold: 2,
  successThreshold: 1,
  timeout: 500,
  monitoringWindow: 2000,
  expectedErrors: [Error],
  fallback: () => 'fallback',
});
expectType<CircuitBreaker>(breakerWithFallback);
expectType<Promise<string>>(breakerWithFallback.execute(async () => 'ok'));

// Test Quality Policy types
const policy = loadQualityPolicy('ci');
expectType<QualityPolicy>(policy);
expectType<string>(policy.title);
expectType<string>(policy.version);
expectType<object>(policy.quality);