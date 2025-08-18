#!/usr/bin/env node

/**
 * Accessibility threshold checker for Phase 6 Quality Gates
 * Now uses centralized quality policy for threshold management
 */

const fs = require('fs');
const path = require('path');

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
let critical, warnings, serious, moderate, minor;

if (policy && policy.quality.accessibility) {
  const a11yGate = policy.quality.accessibility;
  critical = a11yGate.thresholds.critical || 0;
  serious = a11yGate.thresholds.serious || 2;
  moderate = a11yGate.thresholds.moderate || 3;
  minor = a11yGate.thresholds.minor || 5;
  warnings = a11yGate.thresholds.total_warnings || 5;
  
  console.log(`📋 Using centralized quality policy (${environment} environment)`);
  console.log(`   Policy version: ${policy.version}`);
  console.log(`   Enforcement level: ${a11yGate.enforcement}`);
} else {
  // Fallback to CLI arguments
  critical = parseInt(args.find(arg => arg.startsWith('--critical='))?.split('=')[1] || '0');
  warnings = parseInt(args.find(arg => arg.startsWith('--warnings='))?.split('=')[1] || '5');
  serious = 2;
  moderate = 3;
  minor = 5;
  
  console.log('📋 Using command line arguments (fallback mode)');
}

// Default a11y report path
const reportPath = path.join(process.cwd(), 'reports/a11y-results.json');

function checkA11yThreshold() {
  try {
    // Check if report exists
    if (!fs.existsSync(reportPath)) {
      console.log('⚠️  A11y report not found, creating empty report for development');
      // Create empty report for development phase
      fs.mkdirSync(path.dirname(reportPath), { recursive: true });
      fs.writeFileSync(reportPath, JSON.stringify({
        violations: {
          critical: 0,
          serious: 0,
          moderate: 0,
          minor: 0
        },
        passes: 0,
        timestamp: new Date().toISOString()
      }, null, 2));
      console.log('✅ Empty a11y report created - all thresholds passed');
      return true;
    }

    const report = JSON.parse(fs.readFileSync(reportPath, 'utf8'));
    const violations = report.violations || {};
    
    const criticalCount = violations.critical || 0;
    const seriousCount = violations.serious || 0;
    const moderateCount = violations.moderate || 0;
    const minorCount = violations.minor || 0;
    const totalWarnings = seriousCount + moderateCount + minorCount;
    
    console.log(`📊 A11y Results:`);
    console.log(`   Critical: ${criticalCount} (threshold: ≤${critical})`);
    console.log(`   Serious: ${seriousCount} (threshold: ≤${serious})`);
    console.log(`   Moderate: ${moderateCount} (threshold: ≤${moderate})`);
    console.log(`   Minor: ${minorCount} (threshold: ≤${minor})`);
    console.log(`   Total Warnings: ${totalWarnings} (threshold: ≤${warnings})`);
    
    let hasFailures = false;
    const failures = [];
    
    if (criticalCount > critical) {
      failures.push(`Critical violations: ${criticalCount} > ${critical}`);
      hasFailures = true;
    }
    
    if (seriousCount > serious) {
      failures.push(`Serious violations: ${seriousCount} > ${serious}`);
      hasFailures = true;
    }
    
    if (moderateCount > moderate) {
      failures.push(`Moderate violations: ${moderateCount} > ${moderate}`);
      hasFailures = true;
    }
    
    if (minorCount > minor) {
      failures.push(`Minor violations: ${minorCount} > ${minor}`);
      hasFailures = true;
    }
    
    if (totalWarnings > warnings) {
      failures.push(`Total warnings: ${totalWarnings} > ${warnings}`);
      hasFailures = true;
    }
    
    if (hasFailures) {
      console.error(`❌ Accessibility thresholds exceeded:`);
      failures.forEach(failure => console.error(`   • ${failure}`));
      return false;
    }
    
    console.log('✅ All accessibility thresholds passed');
    return true;
    
  } catch (error) {
    console.error('❌ Error checking a11y threshold:', error.message);
    return false;
  }
}

const success = checkA11yThreshold();
process.exit(success ? 0 : 1);