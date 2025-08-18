#!/usr/bin/env node

/**
 * Quality Policy Validation Tool
 * Validates the centralized quality policy configuration
 */

const fs = require('fs');
const path = require('path');

/**
 * JSON Schema validation for quality policy structure
 */
const REQUIRED_FIELDS = {
  policy: ['title', 'description', 'version', 'quality'],
  gate: ['description', 'enforcement', 'thresholds', 'tools', 'phases'],
  environment: ['description', 'overrides']
};

const VALID_ENFORCEMENT_LEVELS = ['strict', 'warn', 'off'];
const VALID_PHASES = ['phase-1', 'phase-2', 'phase-3', 'phase-4', 'phase-5', 'phase-6'];

/**
 * Validate policy file structure and content
 */
function validateQualityPolicy() {
  console.log('🔍 Validating Quality Policy Configuration...');
  
  const policyPath = path.join(process.cwd(), 'policy', 'quality.json');
  
  // Check if policy file exists
  if (!fs.existsSync(policyPath)) {
    console.error('❌ Policy file not found:', policyPath);
    return false;
  }
  
  try {
    // Parse JSON
    const policyContent = fs.readFileSync(policyPath, 'utf-8');
    const policy = JSON.parse(policyContent);
    
    console.log('✅ Policy file is valid JSON');
    console.log(`   Version: ${policy.version || 'Unknown'}`);
    console.log(`   Last updated: ${policy.lastUpdated || 'Unknown'}`);
    
    let isValid = true;
    const warnings = [];
    const errors = [];
    
    // Validate required top-level fields
    for (const field of REQUIRED_FIELDS.policy) {
      if (!policy[field]) {
        errors.push(`Missing required field: ${field}`);
        isValid = false;
      }
    }
    
    // Validate quality gates
    if (policy.quality) {
      console.log(`\\n📋 Found ${Object.keys(policy.quality).length} quality gates:`);
      
      for (const [gateName, gate] of Object.entries(policy.quality)) {
        console.log(`   • ${gateName}: ${gate.description || 'No description'}`);
        
        // Validate gate structure
        for (const field of REQUIRED_FIELDS.gate) {
          if (!gate[field]) {
            errors.push(`Gate '${gateName}' missing required field: ${field}`);
            isValid = false;
          }
        }
        
        // Validate enforcement level
        if (gate.enforcement && !VALID_ENFORCEMENT_LEVELS.includes(gate.enforcement)) {
          errors.push(`Gate '${gateName}' has invalid enforcement level: ${gate.enforcement}`);
          isValid = false;
        }
        
        // Validate phases
        if (gate.phases) {
          for (const phase of gate.phases) {
            if (!VALID_PHASES.includes(phase)) {
              warnings.push(`Gate '${gateName}' references unknown phase: ${phase}`);
            }
          }
        }
        
        if (gate.enabledFromPhase && !VALID_PHASES.includes(gate.enabledFromPhase)) {
          warnings.push(`Gate '${gateName}' has invalid enabledFromPhase: ${gate.enabledFromPhase}`);
        }
        
        // Validate thresholds are numeric where expected
        if (gate.thresholds) {
          for (const [metric, value] of Object.entries(gate.thresholds)) {
            if (typeof value !== 'number' && typeof value !== 'string') {
              warnings.push(`Gate '${gateName}' threshold '${metric}' should be number or string, got: ${typeof value}`);
            }
          }
        }
        
        // Check for empty tool arrays
        if (gate.tools && gate.tools.length === 0) {
          warnings.push(`Gate '${gateName}' has empty tools array`);
        }
      }
    }
    
    // Validate environments
    if (policy.environments) {
      console.log(`\\n🌍 Found ${Object.keys(policy.environments).length} environment configurations:`);
      
      for (const [envName, env] of Object.entries(policy.environments)) {
        console.log(`   • ${envName}: ${env.description || 'No description'}`);
        
        // Validate environment structure
        for (const field of REQUIRED_FIELDS.environment) {
          if (!env[field]) {
            warnings.push(`Environment '${envName}' missing recommended field: ${field}`);
          }
        }
        
        // Validate override paths
        if (env.overrides) {
          for (const [overridePath, value] of Object.entries(env.overrides)) {
            const pathParts = overridePath.split('.');
            
            if (pathParts.length < 2) {
              warnings.push(`Environment '${envName}' override path '${overridePath}' seems too short`);
            }
            
            const gateName = pathParts[0];
            if (!policy.quality[gateName]) {
              warnings.push(`Environment '${envName}' override references unknown gate: ${gateName}`);
            }
          }
        }
      }
    }
    
    // Validate reporting configuration
    if (policy.reporting) {
      const reporting = policy.reporting;
      
      if (!reporting.outputDirectory) {
        warnings.push('Reporting configuration missing outputDirectory');
      }
      
      if (!reporting.formats || !Array.isArray(reporting.formats)) {
        warnings.push('Reporting configuration missing or invalid formats array');
      }
      
      if (reporting.retention && typeof reporting.retention.days !== 'number') {
        warnings.push('Reporting retention days should be a number');
      }
    }
    
    // Print results
    console.log('\\n📊 Validation Results:');
    
    if (errors.length > 0) {
      console.log(`\\n❌ Errors (${errors.length}):`);
      errors.forEach(error => console.log(`   • ${error}`));
    }
    
    if (warnings.length > 0) {
      console.log(`\\n⚠️  Warnings (${warnings.length}):`);
      warnings.forEach(warning => console.log(`   • ${warning}`));
    }
    
    if (isValid) {
      console.log('\\n✅ Policy validation completed successfully');
      
      if (warnings.length === 0) {
        console.log('🎉 No issues found!');
      } else {
        console.log(`💡 Consider addressing ${warnings.length} warnings for optimal configuration`);
      }
    } else {
      console.log('\\n❌ Policy validation failed');
      console.log(`🔧 Please fix ${errors.length} errors before using this policy`);
    }
    
    return isValid;
    
  } catch (error) {
    if (error instanceof SyntaxError) {
      console.error('❌ Invalid JSON in policy file:', error.message);
    } else {
      console.error('❌ Error validating policy:', error.message);
    }
    return false;
  }
}

/**
 * Show example policy structure
 */
function showExample() {
  console.log(`
Example Quality Policy Structure:

{
  "title": "AE-Framework Quality Gates Policy",
  "description": "Centralized quality gates configuration",
  "version": "1.0.0",
  "lastUpdated": "2025-01-20T10:00:00Z",
  
  "quality": {
    "accessibility": {
      "description": "Accessibility compliance thresholds",
      "enforcement": "strict",
      "thresholds": {
        "critical": 0,
        "total_warnings": 5
      },
      "tools": ["jest-axe", "axe-core"],
      "phases": ["phase-6"]
    }
  },
  
  "environments": {
    "development": {
      "description": "Development environment overrides",
      "overrides": {
        "accessibility.thresholds.total_warnings": 10
      }
    }
  }
}
`);
}

// Show help if requested
if (process.argv.includes('--help') || process.argv.includes('-h')) {
  console.log(`
Quality Policy Validation Tool

USAGE:
  node scripts/validate-quality-policy.cjs [OPTIONS]

OPTIONS:
  --example           Show example policy structure
  --help, -h          Show this help message

EXAMPLES:
  node scripts/validate-quality-policy.cjs          # Validate current policy
  node scripts/validate-quality-policy.cjs --example # Show example structure
`);
  process.exit(0);
}

if (process.argv.includes('--example')) {
  showExample();
  process.exit(0);
}

// Run validation
const success = validateQualityPolicy();
process.exit(success ? 0 : 1);