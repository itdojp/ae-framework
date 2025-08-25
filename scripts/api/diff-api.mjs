#!/usr/bin/env node
/**
 * API Breaking Change Detector
 * 
 * Compares current API report with baseline and identifies breaking changes:
 * - Removals (functions, classes, interfaces, properties)
 * - Signature changes (parameter types, return types, etc.)
 * - Additions are considered non-breaking
 * 
 * Exit codes:
 * - 0: No breaking changes
 * - 3: Breaking changes detected (blocked unless ALLOW_API_BREAKING=1)
 * - 1: Error in processing
 */

import { readFile, access, constants } from 'node:fs/promises';
import { glob } from 'glob';
import path from 'node:path';

/**
 * Check if file exists
 * @param {string} filePath 
 * @returns {Promise<boolean>}
 */
async function fileExists(filePath) {
  try {
    await access(filePath, constants.F_OK);
    return true;
  } catch {
    return false;
  }
}

/**
 * Parse API report into structured data
 * @param {string} content - API report content
 * @returns {Set<string>} Set of API signatures
 */
function parseApiReport(content) {
  const signatures = new Set();
  const lines = content.split('\n');
  
  for (const line of lines) {
    const trimmed = line.trim();
    if (trimmed && !trimmed.startsWith('//') && !trimmed.startsWith('/*')) {
      // Extract meaningful API signatures (functions, classes, interfaces, etc.)
      if (trimmed.match(/^(export |declare |function |class |interface |type |const |let |var )/)) {
        signatures.add(trimmed);
      }
    }
  }
  
  return signatures;
}

/**
 * Identify breaking changes between API reports
 * @param {Set<string>} baseline - Baseline API signatures
 * @param {Set<string>} current - Current API signatures
 * @returns {object} Analysis result
 */
function analyzeChanges(baseline, current) {
  const removed = new Set();
  const added = new Set();
  const modified = new Set();
  
  // Check for removals (breaking)
  for (const sig of baseline) {
    if (!current.has(sig)) {
      // Check if it's a modification rather than pure removal
      const baseSignature = sig.split('(')[0].split(':')[0].trim();
      let isModification = false;
      
      for (const currentSig of current) {
        const currentBase = currentSig.split('(')[0].split(':')[0].trim();
        if (baseSignature === currentBase) {
          modified.add({ from: sig, to: currentSig });
          isModification = true;
          break;
        }
      }
      
      if (!isModification) {
        removed.add(sig);
      }
    }
  }
  
  // Check for additions (non-breaking)
  for (const sig of current) {
    if (!baseline.has(sig)) {
      const currentSignature = sig.split('(')[0].split(':')[0].trim();
      let isModification = false;
      
      for (const baseSig of baseline) {
        const baseSignature = baseSig.split('(')[0].split(':')[0].trim();
        if (currentSignature === baseSignature) {
          isModification = true;
          break;
        }
      }
      
      if (!isModification) {
        added.add(sig);
      }
    }
  }
  
  return {
    removed: Array.from(removed),
    added: Array.from(added),
    modified: Array.from(modified),
    breaking: removed.size + modified.size > 0
  };
}

/**
 * Main function
 */
async function main() {
  console.log('[api:diff] Analyzing API changes for breaking changes...');
  
  try {
    // Find generated API report
    const apiReports = await glob('artifacts/api/*.api.md');
    if (apiReports.length === 0) {
      console.log('❌ No API report found. Run `pnpm api:report` first.');
      process.exit(1);
    }
    
    if (apiReports.length > 1) {
      console.log(`⚠️  Multiple API reports found: ${apiReports.join(', ')}. Using first one.`);
    }
    
    const currentReportPath = apiReports[0];
    const baselineReportPath = 'api/public.api.md';
    
    console.log(`[api:diff] Current report: ${currentReportPath}`);
    console.log(`[api:diff] Baseline report: ${baselineReportPath}`);
    
    // Check if baseline exists
    if (!(await fileExists(baselineReportPath))) {
      console.log('ℹ️  No baseline API report found. This appears to be the initial API definition.');
      console.log(`💡 To establish baseline: cp "${currentReportPath}" "${baselineReportPath}"`);
      console.log('✅ No breaking changes (initial API)');
      process.exit(0);
    }
    
    // Read both reports
    const currentContent = await readFile(currentReportPath, 'utf8');
    const baselineContent = await readFile(baselineReportPath, 'utf8');
    
    // Parse API signatures
    const currentSignatures = parseApiReport(currentContent);
    const baselineSignatures = parseApiReport(baselineContent);
    
    console.log(`[api:diff] Baseline API signatures: ${baselineSignatures.size}`);
    console.log(`[api:diff] Current API signatures: ${currentSignatures.size}`);
    
    // Analyze changes
    const analysis = analyzeChanges(baselineSignatures, currentSignatures);
    
    // Report results
    console.log('\n📊 API Change Analysis:');
    console.log(`  • Added: ${analysis.added.length} (non-breaking)`);
    console.log(`  • Removed: ${analysis.removed.length} (breaking)`);
    console.log(`  • Modified: ${analysis.modified.length} (breaking)`);
    console.log(`  • Breaking changes: ${analysis.breaking ? 'YES' : 'NO'}`);
    
    // Detailed breakdown
    if (analysis.added.length > 0) {
      console.log('\n✅ Added (non-breaking):');
      for (const sig of analysis.added.slice(0, 5)) { // Show first 5
        console.log(`  + ${sig}`);
      }
      if (analysis.added.length > 5) {
        console.log(`  ... and ${analysis.added.length - 5} more`);
      }
    }
    
    if (analysis.removed.length > 0) {
      console.log('\n❌ Removed (breaking):');
      for (const sig of analysis.removed) {
        console.log(`  - ${sig}`);
      }
    }
    
    if (analysis.modified.length > 0) {
      console.log('\n🔄 Modified (breaking):');
      for (const mod of analysis.modified.slice(0, 3)) { // Show first 3
        console.log(`  ~ ${mod.from}`);
        console.log(`    → ${mod.to}`);
      }
      if (analysis.modified.length > 3) {
        console.log(`  ... and ${analysis.modified.length - 3} more modifications`);
      }
    }
    
    // Summary output for verify.md integration
    const summary = `
## API Breaking Change Analysis
- **Added**: ${analysis.added.length} signatures (non-breaking)
- **Removed**: ${analysis.removed.length} signatures (breaking)
- **Modified**: ${analysis.modified.length} signatures (breaking)
- **Status**: ${analysis.breaking ? '❌ BREAKING CHANGES DETECTED' : '✅ No breaking changes'}

${analysis.breaking ? '💡 To accept these changes, set `ALLOW_API_BREAKING=1` or update baseline with `cp "${currentReportPath}" "${baselineReportPath}"`' : ''}
`;
    
    console.log(summary);
    
    // Check environment override
    const allowBreaking = process.env.ALLOW_API_BREAKING === '1';
    
    if (analysis.breaking && !allowBreaking) {
      console.log('🚫 Breaking changes detected and ALLOW_API_BREAKING is not set.');
      console.log('\nTo proceed with breaking changes:');
      console.log('  1. Set ALLOW_API_BREAKING=1 environment variable, or');
      console.log(`  2. Update baseline: cp "${currentReportPath}" "${baselineReportPath}"`);
      console.log('  3. Ensure proper semantic versioning (major version bump)');
      process.exit(3);
    }
    
    if (analysis.breaking && allowBreaking) {
      console.log('⚠️  Breaking changes allowed by ALLOW_API_BREAKING=1');
    }
    
    console.log('✅ API change analysis complete');
    process.exit(0);
    
  } catch (error) {
    console.error(`[api:diff] Error: ${error.message}`);
    process.exit(1);
  }
}

// Run if called directly
if (import.meta.url === `file://${process.argv[1]}`) {
  main();
}