#!/usr/bin/env npx tsx

/**
 * Script to execute Phase 4: Code Generation & Implementation
 */

import { Phase4CodeGeneration } from '../src/self-improvement/phase4-code-generation.js';
import * as fs from 'fs/promises';
import * as path from 'path';

async function main() {
  console.log('🚀 Starting ae-framework Phase 4: Code Generation & Implementation...\n');
  
  const phase4 = new Phase4CodeGeneration();
  
  try {
    const startTime = Date.now();
    const results = await phase4.executePhase4();
    const endTime = Date.now();
    const duration = Math.round((endTime - startTime) / 1000);
    
    // Generate and display report
    const report = phase4.generatePhase4Report(results);
    console.log('\n' + report);
    
    // Save comprehensive results
    const reportPath = path.join(process.cwd(), 'temp-reports', 'phase4-code-generation.md');
    await fs.mkdir(path.dirname(reportPath), { recursive: true });
    await fs.writeFile(reportPath, report);
    
    const resultsPath = path.join(process.cwd(), 'temp-reports', 'phase4-results.json');
    await fs.writeFile(resultsPath, JSON.stringify(results, null, 2));
    
    console.log(`\n📄 Report saved to: ${reportPath}`);
    console.log(`📊 Results saved to: ${resultsPath}`);
    console.log(`⏱️ Phase 4 completed in ${duration} seconds`);
    
    // Status summary
    if (results.overallSuccess) {
      console.log(`\n🎯 Phase 4 SUCCESS: ${results.errorsResolved} errors resolved!`);
      if (results.errorsRemaining === 0) {
        console.log('🏆 ALL TypeScript errors have been resolved!');
        console.log('🚀 Ready for final verification and deployment');
      } else {
        console.log(`🔄 ${results.errorsRemaining} errors remaining - proceed to Phase 5`);
      }
    } else {
      console.log('\n⚠️ Phase 4 PARTIAL SUCCESS: Some fixes applied but verification needed');
      console.log(`📈 Quality improvement: ${results.codeQualityImprovement}%`);
      console.log('🔧 Consider manual review of complex errors');
    }
    
    // Display fix summary
    const highConfidenceFixes = results.fixes.filter(f => f.confidence >= 80);
    if (highConfidenceFixes.length > 0) {
      console.log(`\n✅ High-confidence fixes applied: ${highConfidenceFixes.length}`);
      highConfidenceFixes.slice(0, 3).forEach(fix => {
        console.log(`   - ${path.basename(fix.file)}:${fix.errorLine} (${fix.errorCode})`);
      });
    }
    
    process.exit(results.overallSuccess ? 0 : 1);
    
  } catch (error) {
    console.error('\n❌ Phase 4 execution failed:', error);
    
    // Save error details  
    const errorPath = path.join(process.cwd(), 'temp-reports', 'phase4-error.log');
    await fs.mkdir(path.dirname(errorPath), { recursive: true });
    await fs.writeFile(errorPath, `Phase 4 Error: ${error}\n\nStack: ${error.stack}`);
    
    console.log(`📝 Error details saved to: ${errorPath}`);
    process.exit(1);
  }
}

if (import.meta.url === `file://${process.argv[1]}`) {
  main();
}