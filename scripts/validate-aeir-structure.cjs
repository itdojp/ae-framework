#!/usr/bin/env node

/**
 * AE-IR Structure Validation Script
 * Validates that an AE-IR file has the required structure
 */

const fs = require('fs');

function validateAEIRStructure(filePath) {
  try {
    if (!fs.existsSync(filePath)) {
      console.error(`❌ AE-IR file not found: ${filePath}`);
      process.exit(1);
    }

    const ir = JSON.parse(fs.readFileSync(filePath, 'utf8'));
    const required = ['version', 'metadata', 'domain', 'api'];
    
    for (const field of required) {
      if (!ir[field]) {
        console.error(`❌ Missing required field: ${field}`);
        process.exit(1);
      }
    }
    
    console.log('✅ AE-IR structure validation passed');
    console.log(`   File: ${filePath}`);
    console.log(`   Version: ${ir.version || 'unknown'}`);
    console.log(`   Entities: ${ir.domain?.length ?? 0}`);
    console.log(`   API Endpoints: ${ir.api?.length ?? 0}`);
    
    return true;
  } catch (error) {
    console.error(`❌ AE-IR validation failed: ${error.message}`);
    process.exit(1);
  }
}

// Command line usage
if (require.main === module) {
  const filePath = process.argv[2];
  if (!filePath) {
    console.error('Usage: node validate-aeir-structure.cjs <file-path>');
    process.exit(1);
  }
  
  validateAEIRStructure(filePath);
}

module.exports = { validateAEIRStructure };