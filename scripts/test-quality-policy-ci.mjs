#!/usr/bin/env node
/**
 * Quality Policy CI Profile Test Script
 * Verifies that CI environment configurations are applied correctly
 */

import { loadQualityPolicy, getQualityGate, getThreshold } from '../dist/utils/quality-policy-loader.js';

async function testQualityPolicyCI() {
  console.log('🔍 Quality Policy CI Configuration Test');
  console.log('======================================');

  try {
    // Load policies for different environments
    console.log('\n=== Loading Quality Policies ===');
    
    const defaultPolicy = loadQualityPolicy();
    const devPolicy = loadQualityPolicy('development');
    const ciPolicy = loadQualityPolicy('ci');
    const prodPolicy = loadQualityPolicy('production');
    
    console.log('✅ Successfully loaded all environment policies');
    
    // Debug: check original policy before overrides
    const fs = await import('fs');
    const path = await import('path');
    const originalPolicyContent = fs.readFileSync(path.join(process.cwd(), 'policy', 'quality.json'), 'utf-8');
    const originalPolicy = JSON.parse(originalPolicyContent);
    
    console.log('Debug - Original lighthouse numberOfRuns:', originalPolicy.quality.lighthouse.config.numberOfRuns);
    console.log('Debug - Default policy lighthouse numberOfRuns:', defaultPolicy.quality.lighthouse.config.numberOfRuns);
    console.log('Debug - CI policy lighthouse numberOfRuns:', ciPolicy.quality.lighthouse.config.numberOfRuns);

    // Test CI-specific overrides
    console.log('\n=== CI Environment Overrides ===');
    
    const testCases = [
      // Coverage thresholds should be stricter in CI (original: 80, CI: 85)
      { gate: 'coverage', metric: 'lines', expected: 85, original: 80 },
      { gate: 'coverage', metric: 'functions', expected: 85, original: 80 },
      { gate: 'coverage', metric: 'branches', expected: 80, original: 80 },
      { gate: 'coverage', metric: 'statements', expected: 85, original: 80 },
      
      // Accessibility should be stricter in CI
      { gate: 'accessibility', metric: 'critical', expected: 0, original: 0 },
      { gate: 'accessibility', metric: 'serious', expected: 0, original: 2 },
      { gate: 'accessibility', metric: 'moderate', expected: 1, original: 3 },
      { gate: 'accessibility', metric: 'total_warnings', expected: 3, original: 5 },
      
      // Linting should be stricter in CI
      { gate: 'linting', metric: 'errors', expected: 0, original: 0 },
      { gate: 'linting', metric: 'warnings', expected: 5, original: 10 },
      
      // Security should be strict in CI
      { gate: 'security', metric: 'critical', expected: 0, original: 0 },
      { gate: 'security', metric: 'high', expected: 0, original: 0 },
      { gate: 'security', metric: 'moderate', expected: 1, original: 2 },
      { gate: 'security', metric: 'low', expected: 3, original: 5 },
      
      // Policy enforcement should be strict
      { gate: 'policy', metric: 'uiViolations', expected: 0, original: 0 },
      { gate: 'policy', metric: 'designSystemViolations', expected: 1, original: 0 },
      { gate: 'policy', metric: 'accessibilityViolations', expected: 0, original: 0 },
      
      // TDD should be adjusted for CI (original: 1.2, CI: 1.0)
      { gate: 'tdd', metric: 'testToCodeRatio', expected: 1.0, original: 1.2 }
    ];

    let passed = 0;
    let failed = 0;

    for (const testCase of testCases) {
      const originalValue = originalPolicy.quality[testCase.gate]?.thresholds[testCase.metric] ?? testCase.original;
      const ciValue = getThreshold(testCase.gate, testCase.metric, 'ci');
      
      const success = ciValue === testCase.expected;
      const stricterThanOriginal = testCase.expected !== originalValue;
      const status = success ? '✅' : '❌';
      const improvement = stricterThanOriginal ? '📈' : '➡️';
      
      console.log(`${status} ${improvement} ${testCase.gate}.${testCase.metric}: CI=${ciValue}, Original=${originalValue}, Expected=${testCase.expected}`);
      
      if (success) {
        passed++;
      } else {
        failed++;
        console.log(`   ⚠️  Expected ${testCase.expected} but got ${ciValue}`);
      }
    }

    // Test enforcement changes
    console.log('\n=== Enforcement Changes in CI ===');
    
    const enforcementTests = [
      { gate: 'lighthouse', expected: 'warn' },
      { gate: 'visual', expected: 'off' },
      { gate: 'mutation', expected: 'off' }
    ];

    for (const test of enforcementTests) {
      const defaultGate = getQualityGate(test.gate);
      const ciGate = getQualityGate(test.gate, 'ci');
      
      const success = ciGate.enforcement === test.expected;
      const status = success ? '✅' : '❌';
      
      console.log(`${status} ${test.gate}.enforcement: CI=${ciGate.enforcement}, Default=${defaultGate.enforcement}, Expected=${test.expected}`);
      
      if (success) {
        passed++;
      } else {
        failed++;
      }
    }

    // Test lighthouse config optimization (compare against original policy)
    console.log('\n=== Lighthouse CI Optimization ===');
    
    const originalRuns = originalPolicy.quality.lighthouse.config.numberOfRuns;
    const ciLighthouse = getQualityGate('lighthouse', 'ci');
    const ciRuns = ciLighthouse.config?.numberOfRuns || 3;
    
    const runsOptimized = ciRuns < originalRuns;
    const runsStatus = runsOptimized ? '✅' : '❌';
    
    console.log(`${runsStatus} lighthouse.config.numberOfRuns: CI=${ciRuns}, Original=${originalRuns} (${runsOptimized ? 'Optimized for CI' : 'Not optimized for CI'})`);
    
    if (runsOptimized) {
      passed++;
    } else {
      failed++;
    }

    // Environment comparison summary
    console.log('\n=== Environment Comparison Summary ===');
    
    const environments = [
      { name: 'Default', policy: defaultPolicy },
      { name: 'Development', policy: devPolicy },
      { name: 'CI', policy: ciPolicy },
      { name: 'Production', policy: prodPolicy }
    ];

    for (const env of environments) {
      const overrideCount = Object.keys(env.policy.environments.ci?.overrides || {}).length;
      console.log(`📊 ${env.name}: ${overrideCount} CI overrides applied`);
    }

    // Final results
    console.log('\n=== Test Results ===');
    console.log(`✅ Passed: ${passed}`);
    console.log(`❌ Failed: ${failed}`);
    console.log(`📊 Total: ${passed + failed}`);
    
    const success = failed === 0;
    console.log(`\n${success ? '🎉' : '💥'} CI Quality Policy ${success ? 'Working Correctly' : 'Has Issues'}!`);
    
    if (success) {
      console.log('\n📋 CI Profile Benefits:');
      console.log('• Stricter coverage thresholds (85% vs 80%)');
      console.log('• Zero tolerance for critical accessibility/security issues');
      console.log('• Reduced lighthouse runs for faster CI (1 vs 3 runs)');
      console.log('• Disabled visual regression and mutation testing for speed');
      console.log('• Balanced TDD requirements for CI efficiency');
    }

    return success;

  } catch (error) {
    console.error('❌ Test failed with error:', error.message);
    return false;
  }
}

// Run the test
testQualityPolicyCI()
  .then(success => {
    console.log(`\n🏁 Test completed. Success: ${success}`);
    process.exit(success ? 0 : 1);
  })
  .catch(error => {
    console.error('💥 Test crashed:', error);
    process.exit(1);
  });