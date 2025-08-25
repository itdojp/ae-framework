#!/usr/bin/env node
/**
 * @ts-expect-error policy checker
 * 
 * Enforces structured @ts-expect-error comments with:
 * - owner: GitHub handle
 * - expires: YYYY-MM-DD date (must be today or future)
 * - reason: Description ≥12 characters
 * 
 * Example: // @ts-expect-error owner:@alice expires:2025-12-31 reason: narrowing todo
 */

import { glob } from 'glob';
import { readFile } from 'node:fs/promises';
import path from 'node:path';

/**
 * Parse @ts-expect-error line for policy compliance
 * @param {string} line - Line containing @ts-expect-error
 * @param {string} filePath - File path for error reporting
 * @param {number} lineNumber - Line number for error reporting
 * @returns {object|null} Violation details or null if compliant
 */
function checkExpectErrorLine(line, filePath, lineNumber) {
  // Extract owner, expires, reason from the line
  const ownerMatch = line.match(/owner:\s*@?(\w+)/);
  const expiresMatch = line.match(/expires:\s*(\d{4}-\d{2}-\d{2})/);
  const reasonMatch = line.match(/reason:\s*(.+?)(?:\s*(?:owner:|expires:|$))/);
  
  const violations = [];
  
  // Check owner
  if (!ownerMatch) {
    violations.push('missing owner (format: owner:@username)');
  }
  
  // Check expires
  if (!expiresMatch) {
    violations.push('missing expires (format: expires:YYYY-MM-DD)');
  } else {
    const expiryDate = new Date(expiresMatch[1]);
    const today = new Date();
    today.setHours(0, 0, 0, 0); // Start of today
    
    if (expiryDate < today) {
      violations.push(`expires date ${expiresMatch[1]} is in the past`);
    }
  }
  
  // Check reason
  if (!reasonMatch) {
    violations.push('missing reason (format: reason:description)');
  } else {
    const reason = reasonMatch[1].trim();
    if (reason.length < 12) {
      violations.push(`reason too short: "${reason}" (minimum 12 characters)`);
    }
  }
  
  if (violations.length > 0) {
    return {
      file: filePath,
      line: lineNumber,
      content: line.trim(),
      violations
    };
  }
  
  return null;
}

/**
 * Check a single file for @ts-expect-error policy compliance
 * @param {string} filePath - Path to TypeScript file
 * @returns {Promise<object[]>} Array of violations
 */
async function checkFile(filePath) {
  try {
    const content = await readFile(filePath, 'utf8');
    const lines = content.split('\n');
    const violations = [];
    
    lines.forEach((line, index) => {
      if (line.includes('@ts-expect-error')) {
        const violation = checkExpectErrorLine(line, filePath, index + 1);
        if (violation) {
          violations.push(violation);
        }
      }
    });
    
    return violations;
  } catch (error) {
    console.error(`Warning: Could not read ${filePath}: ${error.message}`);
    return [];
  }
}

/**
 * Main function to check all TypeScript files
 */
async function main() {
  console.log('[expect-error-policy] Scanning TypeScript files for @ts-expect-error policy compliance...');
  
  try {
    // Find all TypeScript files in src/
    const files = await glob('src/**/*.ts', { 
      ignore: ['**/*.test.ts', '**/*.spec.ts', '**/node_modules/**']
    });
    
    console.log(`[expect-error-policy] Checking ${files.length} TypeScript files...`);
    
    let allViolations = [];
    
    // Check each file
    for (const file of files) {
      const violations = await checkFile(file);
      allViolations.push(...violations);
    }
    
    // Report results
    if (allViolations.length === 0) {
      console.log('✅ All @ts-expect-error comments comply with policy');
      process.exit(0);
    }
    
    console.log(`❌ Found ${allViolations.length} @ts-expect-error policy violations:\n`);
    
    // Group violations by file for better readability
    const violationsByFile = allViolations.reduce((acc, violation) => {
      if (!acc[violation.file]) {
        acc[violation.file] = [];
      }
      acc[violation.file].push(violation);
      return acc;
    }, {});
    
    // Output violations
    for (const [file, violations] of Object.entries(violationsByFile)) {
      console.log(`📁 ${file}:`);
      for (const violation of violations) {
        console.log(`  Line ${violation.line}: ${violation.content}`);
        for (const issue of violation.violations) {
          console.log(`    ❌ ${issue}`);
        }
        console.log('');
      }
    }
    
    console.log('Policy format: // @ts-expect-error owner:@username expires:YYYY-MM-DD reason:description ≥12chars');
    console.log('Example: // @ts-expect-error owner:@alice expires:2025-12-31 reason: narrowing todo for complex union');
    
    process.exit(2);
    
  } catch (error) {
    console.error(`[expect-error-policy] Error: ${error.message}`);
    process.exit(1);
  }
}

// Run if called directly
if (import.meta.url === `file://${process.argv[1]}`) {
  main();
}