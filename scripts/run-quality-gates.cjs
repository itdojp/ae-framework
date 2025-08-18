#!/usr/bin/env node

/**
 * Centralized Quality Gates Runner
 * Executes quality gates based on centralized policy configuration
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
    console.error(`❌ Could not load quality policy: ${error.message}`);
    process.exit(1);
  }
}

/**
 * Get current phase from project state
 */
function getCurrentPhase() {
  try {
    const phaseStatePath = path.join(process.cwd(), '.ae', 'phase-state.json');
    const phaseState = JSON.parse(fs.readFileSync(phaseStatePath, 'utf-8'));
    return phaseState.currentPhase || 'phase-1';
  } catch {
    return 'phase-1'; // Default to phase-1 if no state file
  }
}

/**
 * Check if a quality gate should be enforced for the current phase
 */
function shouldEnforceGate(gate, currentPhase) {
  // Check if enforcement is disabled
  if (gate.enforcement === 'off') {
    return false;
  }
  
  // Check if the gate applies to the current phase
  if (gate.phases && gate.phases.length > 0) {
    return gate.phases.includes(currentPhase);
  }
  
  // Check if there's an enabled from phase requirement
  if (gate.enabledFromPhase) {
    const phases = ['phase-1', 'phase-2', 'phase-3', 'phase-4', 'phase-5', 'phase-6'];
    const enabledPhaseIndex = phases.indexOf(gate.enabledFromPhase);
    const currentPhaseIndex = phases.indexOf(currentPhase);
    
    return currentPhaseIndex >= enabledPhaseIndex;
  }
  
  return true;
}

/**
 * Execute a quality gate
 */
function executeQualityGate(gateName, gate, environment) {
  console.log(`\n🔍 Executing ${gateName} quality gate...`);
  console.log(`   Enforcement: ${gate.enforcement}`);
  console.log(`   Description: ${gate.description}`);
  
  try {
    let command;
    let success = true;
    
    switch (gateName) {
      case 'accessibility':
        command = `node scripts/check-a11y-threshold.cjs --env=${environment}`;
        break;
        
      case 'coverage':
        command = `node scripts/check-coverage-threshold.cjs --env=${environment}`;
        break;
        
      case 'lighthouse':
        if (fs.existsSync('lighthouserc.js')) {
          command = 'npx @lhci/cli autorun';
        } else {
          console.log('⚠️  Lighthouse CI config not found, skipping');
          return { success: true, skipped: true };
        }
        break;
        
      case 'linting':
        command = 'npm run lint';
        break;
        
      case 'security':
        command = `npm audit --audit-level moderate`;
        break;
        
      case 'tdd':
        command = 'npm run validate-tdd';
        break;
        
      case 'visual':
        if (fs.existsSync('node_modules/chromatic')) {
          command = 'npm run test:visual';
        } else {
          console.log('⚠️  Visual regression testing not configured, skipping');
          return { success: true, skipped: true };
        }
        break;
        
      case 'policy':
        if (fs.existsSync('policies/ui/')) {
          command = 'node scripts/check-opa-compliance.js --ui-violations=0';
        } else {
          console.log('⚠️  OPA policies not found, skipping');
          return { success: true, skipped: true };
        }
        break;
        
      case 'mutation':
        const mutationPaths = gate.targetPaths?.join(',') || 'src/**/*.ts';
        command = `npx stryker run --mutate "${mutationPaths}" --maxTestRunnerReuse 0`;
        break;
        
      default:
        console.log(`⚠️  Unknown quality gate: ${gateName}`);
        return { success: true, skipped: true };
    }
    
    console.log(`🔄 Running: ${command}`);
    execSync(command, { stdio: 'inherit' });
    
    return { success: true, skipped: false };
    
  } catch (error) {
    const isStrict = gate.enforcement === 'strict';
    
    if (isStrict) {
      console.error(`❌ ${gateName} quality gate failed (strict enforcement)`);
      return { success: false, skipped: false, strict: true };
    } else {
      console.warn(`⚠️  ${gateName} quality gate failed (warning only)`);
      return { success: true, skipped: false, warning: true };
    }
  }
}

/**
 * Main execution function
 */
function runQualityGates() {
  const args = process.argv.slice(2);
  const environment = args.find(arg => arg.startsWith('--env='))?.split('=')[1] || 'ci';
  const specificGates = args.find(arg => arg.startsWith('--gates='))?.split('=')[1]?.split(',');
  const currentPhase = args.find(arg => arg.startsWith('--phase='))?.split('=')[1] || getCurrentPhase();
  
  console.log('🚀 AE-Framework Quality Gates Runner');
  console.log(`   Environment: ${environment}`);
  console.log(`   Phase: ${currentPhase}`);
  
  const policy = loadQualityPolicy(environment);
  console.log(`   Policy version: ${policy.version}`);
  console.log(`   Last updated: ${policy.lastUpdated}`);
  
  const results = {
    total: 0,
    passed: 0,
    failed: 0,
    skipped: 0,
    warnings: 0
  };
  
  const gatestoRun = specificGates || Object.keys(policy.quality);
  
  console.log(`\n📋 Quality gates to evaluate: ${gatestoRun.join(', ')}`);
  
  for (const gateName of gatestoRun) {
    const gate = policy.quality[gateName];
    
    if (!gate) {
      console.warn(`⚠️  Quality gate '${gateName}' not found in policy`);
      continue;
    }
    
    results.total++;
    
    // Check if this gate should be enforced for the current phase
    if (!shouldEnforceGate(gate, currentPhase)) {
      console.log(`\n⏭️  Skipping ${gateName} (not applicable for ${currentPhase})`);
      results.skipped++;
      continue;
    }
    
    const result = executeQualityGate(gateName, gate, environment);
    
    if (result.skipped) {
      results.skipped++;
    } else if (result.success) {
      if (result.warning) {
        results.warnings++;
      }
      results.passed++;
    } else {
      results.failed++;
      
      if (result.strict) {
        console.log('\n🚫 Strict quality gate failed - stopping execution');
        break;
      }
    }
  }
  
  // Print summary
  console.log('\n📊 Quality Gates Summary:');
  console.log(`   Total: ${results.total}`);
  console.log(`   Passed: ${results.passed} ✅`);
  console.log(`   Failed: ${results.failed} ❌`);
  console.log(`   Skipped: ${results.skipped} ⏭️`);
  console.log(`   Warnings: ${results.warnings} ⚠️`);
  
  if (results.failed > 0) {
    console.log('\n❌ Quality gates failed');
    process.exit(1);
  } else {
    console.log('\n✅ All quality gates passed');
    process.exit(0);
  }
}

// Show help if requested
if (process.argv.includes('--help') || process.argv.includes('-h')) {
  console.log(`
AE-Framework Quality Gates Runner

USAGE:
  node scripts/run-quality-gates.cjs [OPTIONS]

OPTIONS:
  --env=<environment>     Environment (development, ci, production) [default: ci]
  --phase=<phase>         Current phase (phase-1, phase-2, ..., phase-6) [default: auto-detect]
  --gates=<gates>         Comma-separated list of gates to run [default: all applicable]
  --help, -h              Show this help message

EXAMPLES:
  node scripts/run-quality-gates.cjs                                    # Run all applicable gates
  node scripts/run-quality-gates.cjs --env=development                  # Use development overrides
  node scripts/run-quality-gates.cjs --gates=accessibility,coverage     # Run specific gates
  node scripts/run-quality-gates.cjs --phase=phase-6                    # Force specific phase
`);
  process.exit(0);
}

runQualityGates();