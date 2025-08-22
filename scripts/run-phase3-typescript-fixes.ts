#!/usr/bin/env npx tsx

/**
 * Script to execute Phase 3 TypeScript Error Resolution
 */

import { Phase3TypeScriptFixer } from '../src/self-improvement/phase3-typescript-fixes.js';
import * as fs from 'fs/promises';
import * as path from 'path';

async function main() {
  console.log('🚀 Starting ae-framework Phase 3: TypeScript Error Resolution...\n');
  
  const fixer = new Phase3TypeScriptFixer();
  
  try {
    const startTime = Date.now();
    const results = await fixer.executeSystematicFixes();
    const endTime = Date.now();
    const duration = Math.round((endTime - startTime) / 1000);
    
    // Generate and display report
    const report = fixer.generateFixReport(results);
    console.log('\n' + report);
    
    // Save report
    const reportPath = path.join(process.cwd(), 'temp-reports', 'phase3-typescript-fixes.md');
    await fs.mkdir(path.dirname(reportPath), { recursive: true });
    await fs.writeFile(reportPath, report);
    
    // Save detailed results
    const resultsPath = path.join(process.cwd(), 'temp-reports', 'phase3-fix-results.json');
    await fs.writeFile(resultsPath, JSON.stringify(results, null, 2));
    
    console.log(`\n📄 Report saved to: ${reportPath}`);
    console.log(`📊 Results saved to: ${resultsPath}`);
    console.log(`⏱️ Completed in ${duration} seconds`);
    
    // Status summary
    if (results.errorsFixed > 0) {
      console.log(`\n✅ SUCCESS: ${results.errorsFixed} errors resolved`);
      if (results.errorsRemaining > 0) {
        console.log(`🔄 ${results.errorsRemaining} errors remaining - ready for Phase 4`);
      } else {
        console.log('🎉 ALL TypeScript errors resolved!');
      }
    } else {
      console.log('\n⚠️ No new errors resolved - may need different approach');
    }
    
    process.exit(0);
    
  } catch (error) {
    console.error('\n❌ Phase 3 TypeScript fixes failed:', error);
    
    // Save error details
    const errorPath = path.join(process.cwd(), 'temp-reports', 'phase3-fix-error.log');
    await fs.mkdir(path.dirname(errorPath), { recursive: true });
    await fs.writeFile(errorPath, `Phase 3 Fix Error: ${error}\n\nStack: ${error.stack}`);
    
    console.log(`📝 Error details saved to: ${errorPath}`);
    process.exit(1);
  }
}

if (import.meta.url === `file://${process.argv[1]}`) {
  main();
}