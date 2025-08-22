#!/usr/bin/env node
/**
 * Phase 0 Validation Script
 * Simple validation of TDD infrastructure setup
 */

import { readFileSync, existsSync } from 'fs';
import { join } from 'path';

console.log('\n🚀 ae-framework Self-Improvement Phase 0 Validation');
console.log('='.repeat(60));

let validationsPassed = 0;
let totalValidations = 0;

function validate(description, condition) {
  totalValidations++;
  const status = condition ? '✅' : '❌';
  console.log(`${status} ${description}`);
  if (condition) validationsPassed++;
  return condition;
}

// 1. Check ae-framework-v2.yml exists
validate(
  'ae-framework-v2.yml configuration file exists',
  existsSync('ae-framework-v2.yml')
);

// 2. Check TDD setup source exists
validate(
  'TDD setup source code exists',
  existsSync('src/self-improvement/tdd-setup.ts')
);

// 3. Check TDD setup tests exist
validate(
  'TDD setup tests exist',
  existsSync('tests/self-improvement/tdd-setup.test.ts')
);

// 4. Check git hooks setup exists
validate(
  'Git hooks setup source exists',
  existsSync('src/self-improvement/setup-git-hooks.ts')
);

// 5. Check git hooks tests exist
validate(
  'Git hooks setup tests exist',
  existsSync('tests/self-improvement/setup-git-hooks.test.ts')
);

// 6. Check pre-commit hook exists
validate(
  'Pre-commit hook script exists',
  existsSync('scripts/hooks/pre-commit')
);

// 7. Check demo script exists
validate(
  'Demo script exists',
  existsSync('src/self-improvement/demo.ts')
);

// 8. Validate configuration content
let configValid = false;
if (existsSync('ae-framework-v2.yml')) {
  try {
    const configContent = readFileSync('ae-framework-v2.yml', 'utf8');
    configValid = configContent.includes('self-improvement') && 
                  configContent.includes('0-tdd-setup') &&
                  configContent.includes('version: "2.0"');
  } catch (error) {
    configValid = false;
  }
}
validate(
  'Configuration contains self-improvement settings',
  configValid
);

// 9. Check test directories exist
validate(
  'Tests directory structure exists',
  existsSync('tests') && existsSync('tests/self-improvement')
);

// 10. Check metrics directory can be created
let metricsReady = false;
try {
  const { mkdirSync } = require('fs');
  mkdirSync('metrics/self-improvement', { recursive: true });
  metricsReady = existsSync('metrics/self-improvement');
} catch (error) {
  metricsReady = false;
}
validate(
  'Metrics directory ready',
  metricsReady
);

console.log('\n📊 Phase 0 Validation Summary');
console.log('-'.repeat(40));
console.log(`Validations Passed: ${validationsPassed}/${totalValidations}`);
console.log(`Success Rate: ${Math.round((validationsPassed/totalValidations) * 100)}%`);

const success = validationsPassed === totalValidations;

if (success) {
  console.log('\n✅ Phase 0: TDD Infrastructure Setup - COMPLETE');
  console.log('🚀 Ready to proceed to Phase 1: Foundation Analysis & Core Utilities');
  console.log('\n🎯 Self-Improvement Goals:');
  console.log('   - TypeScript Errors: 287 → 0');
  console.log('   - Test Coverage: → 80%+');
  console.log('   - TDD Compliance: → 95%+');
  console.log('   - Performance: → 20% improvement');
} else {
  console.log('\n❌ Phase 0: TDD Infrastructure Setup - INCOMPLETE');
  console.log('🔧 Fix failed validations before proceeding to Phase 1');
}

console.log('\n🏁 Phase 0 validation completed.');
process.exit(success ? 0 : 1);