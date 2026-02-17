import type { ConformanceVerificationResult } from '../conformance/types.js';

export interface VerificationDisplayOptions {
  verbose?: boolean;
}

export function displayVerificationResults(
  result: ConformanceVerificationResult,
  options: VerificationDisplayOptions = {},
): void {
  console.log('\n📊 Verification Results:\n');

  console.log(`✅ Overall Status: ${result.overall.toUpperCase()}`);
  console.log(`📋 Total Rules: ${result.summary.totalRules}`);
  console.log(`🔧 Rules Executed: ${result.summary.rulesExecuted}`);
  console.log(`✅ Rules Passed: ${result.summary.rulesPassed}`);
  console.log(`❌ Rules Failed: ${result.summary.rulesFailed}`);
  console.log(`⏭️  Rules Skipped: ${result.summary.rulesSkipped}`);
  console.log(`🚨 Rules Error: ${result.summary.rulesError}`);
  console.log(`⏱️  Total Duration: ${result.summary.totalDuration}ms`);
  console.log('');

  if (result.violations.length > 0) {
    console.log('🚨 Violations Found:\n');

    result.violations.forEach((violation, index) => {
      console.log(`${index + 1}. ${violation.ruleName}`);
      console.log(`   Category: ${violation.category}`);
      console.log(`   Severity: ${violation.severity}`);
      console.log(`   Message: ${violation.message}`);
      if (violation.actualValue !== undefined) {
        console.log(`   Actual: ${JSON.stringify(violation.actualValue)}`);
      }
      if (violation.expectedValue !== undefined) {
        console.log(`   Expected: ${JSON.stringify(violation.expectedValue)}`);
      }
      console.log('');
    });

    console.log('📈 Violations by Severity:');
    for (const [severity, count] of Object.entries(result.summary.violationsBySeverity)) {
      if (Number(count) > 0) {
        console.log(`   ${severity}: ${count}`);
      }
    }
    console.log('');

    console.log('📂 Violations by Category:');
    for (const [category, count] of Object.entries(result.summary.violationsByCategory)) {
      if (Number(count) > 0) {
        console.log(`   ${category}: ${count}`);
      }
    }
  } else {
    console.log('🎉 No violations found - all rules passed!');
  }

  if (options.verbose && result.results) {
    console.log('\n📋 Detailed Results:\n');
    result.results.forEach((res, index) => {
      console.log(`${index + 1}. Rule ${res.ruleId}`);
      console.log(`   Status: ${res.status}`);
      console.log(`   Duration: ${res.duration}ms`);
      if (res.violation) {
        console.log(`   Violation: ${res.violation.message}`);
      }
      console.log('');
    });
  }
}
