#!/usr/bin/env node

/**
 * Coverage threshold checker using centralized quality policy
 * Validates coverage test results against defined thresholds
 */

const fs = require('fs');
const path = require('path');
const { execSync } = require('child_process');

/**
 * Load quality policy from centralized configuration
 */
function loadQualityPolicy(environment) {
  try {
    const policyPath = path.join(process.cwd(), 'policy', 'quality.json');
    const policyContent = fs.readFileSync(policyPath, 'utf-8');
    const policy = JSON.parse(policyContent);
    
    // Apply environment overrides if specified
    if (environment && policy.environments[environment]) {
      const overrides = policy.environments[environment].overrides;
      Object.entries(overrides).forEach(([overridePath, value]) => {
        const pathParts = overridePath.split('.');
        let current = policy.quality;
        
        for (let i = 0; i < pathParts.length - 1; i++) {
          current = current[pathParts[i]];
        }
        
        current[pathParts[pathParts.length - 1]] = value;
      });
    }
    
    return policy;
  } catch (error) {
    console.warn(`⚠️  Could not load quality policy: ${error.message}`);
    console.log('🔄 Falling back to command line arguments');
    return null;
  }
}

// Parse command line arguments and load policy
const args = process.argv.slice(2);
const environment = args.find(arg => arg.startsWith('--env='))?.split('=')[1] || 'ci';
const policy = loadQualityPolicy(environment);

// Get thresholds from policy or fallback to CLI args
let linesThreshold, functionsThreshold, branchesThreshold, statementsThreshold;

if (policy && policy.quality.coverage) {
  const coverageGate = policy.quality.coverage;
  linesThreshold = coverageGate.thresholds.lines || 80;
  functionsThreshold = coverageGate.thresholds.functions || 80;
  branchesThreshold = coverageGate.thresholds.branches || 80;
  statementsThreshold = coverageGate.thresholds.statements || 80;
  
  console.log(`📋 Using centralized quality policy (${environment} environment)`);
  console.log(`   Policy version: ${policy.version}`);
  console.log(`   Enforcement level: ${coverageGate.enforcement}`);
} else {
  // Fallback to CLI arguments
  linesThreshold = parseInt(args.find(arg => arg.startsWith('--lines='))?.split('=')[1] || '80');
  functionsThreshold = parseInt(args.find(arg => arg.startsWith('--functions='))?.split('=')[1] || '80');
  branchesThreshold = parseInt(args.find(arg => arg.startsWith('--branches='))?.split('=')[1] || '80');
  statementsThreshold = parseInt(args.find(arg => arg.startsWith('--statements='))?.split('=')[1] || '80');
  
  console.log('📋 Using command line arguments (fallback mode)');
}

/**
 * Check coverage thresholds using nyc
 */
function checkCoverageThreshold() {
  try {
    console.log(`📊 Checking coverage thresholds...`);
    console.log(`   Lines: ≥${linesThreshold}%`);
    console.log(`   Functions: ≥${functionsThreshold}%`);
    console.log(`   Branches: ≥${branchesThreshold}%`);
    console.log(`   Statements: ≥${statementsThreshold}%`);
    
    // Run nyc check-coverage with centralized thresholds
    const command = `npx nyc check-coverage --lines ${linesThreshold} --functions ${functionsThreshold} --branches ${branchesThreshold} --statements ${statementsThreshold}`;
    
    console.log(`🔄 Running: ${command}`);
    execSync(command, { stdio: 'inherit' });
    
    console.log('✅ All coverage thresholds passed');
    return true;
    
  } catch (error) {
    console.error('❌ Coverage threshold check failed');
    
    // Try to extract more detailed information from coverage report
    try {
      const coveragePath = path.join(process.cwd(), 'coverage', 'coverage-summary.json');
      if (fs.existsSync(coveragePath)) {
        const coverage = JSON.parse(fs.readFileSync(coveragePath, 'utf8'));
        const total = coverage.total;
        
        console.log('\n📊 Actual Coverage Results:');
        console.log(`   Lines: ${total.lines.pct}% (threshold: ≥${linesThreshold}%)`);
        console.log(`   Functions: ${total.functions.pct}% (threshold: ≥${functionsThreshold}%)`);
        console.log(`   Branches: ${total.branches.pct}% (threshold: ≥${branchesThreshold}%)`);
        console.log(`   Statements: ${total.statements.pct}% (threshold: ≥${statementsThreshold}%)`);
        
        // Identify which thresholds failed
        const failures = [];
        if (total.lines.pct < linesThreshold) failures.push(`Lines: ${total.lines.pct}% < ${linesThreshold}%`);
        if (total.functions.pct < functionsThreshold) failures.push(`Functions: ${total.functions.pct}% < ${functionsThreshold}%`);
        if (total.branches.pct < branchesThreshold) failures.push(`Branches: ${total.branches.pct}% < ${branchesThreshold}%`);
        if (total.statements.pct < statementsThreshold) failures.push(`Statements: ${total.statements.pct}% < ${statementsThreshold}%`);
        
        if (failures.length > 0) {
          console.log('\n❌ Failed thresholds:');
          failures.forEach(failure => console.log(`   • ${failure}`));
        }
      }
    } catch (reportError) {
      console.warn('⚠️  Could not read coverage report for details');
    }
    
    return false;
  }
}

const success = checkCoverageThreshold();
process.exit(success ? 0 : 1);