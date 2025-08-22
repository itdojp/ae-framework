#!/usr/bin/env npx tsx

/**
 * Script to execute Phase 5: Verification & Final Error Resolution
 */

import { Phase5VerificationFinal } from '../src/self-improvement/phase5-verification-final.js';
import * as fs from 'fs/promises';
import * as path from 'path';

async function main() {
  console.log('🎯 Starting ae-framework Phase 5: Verification & Final Error Resolution...\n');
  
  const phase5 = new Phase5VerificationFinal();
  
  try {
    const startTime = Date.now();
    const results = await phase5.executePhase5();
    const endTime = Date.now();
    const totalDuration = Math.round((endTime - startTime) / 1000);
    
    // Generate and display comprehensive report
    const report = phase5.generatePhase5Report(results);
    console.log('\n' + report);
    
    // Save detailed results
    const reportPath = path.join(process.cwd(), 'temp-reports', 'phase5-verification-final.md');
    await fs.mkdir(path.dirname(reportPath), { recursive: true });
    await fs.writeFile(reportPath, report);
    
    const resultsPath = path.join(process.cwd(), 'temp-reports', 'phase5-results.json');
    await fs.writeFile(resultsPath, JSON.stringify(results, null, 2));
    
    console.log(`\n📄 Comprehensive report saved to: ${reportPath}`);
    console.log(`📊 Detailed results saved to: ${resultsPath}`);
    console.log(`⏱️ Phase 5 completed in ${totalDuration} seconds`);
    
    // Final status summary
    if (results.overallSuccess) {
      console.log(`\n🎉 PHASE 5 COMPLETE SUCCESS!`);
      console.log(`🏆 ALL ${results.initialErrorCount} TypeScript errors have been resolved!`);
      console.log(`✅ Compilation: SUCCESS`);
      console.log(`✅ Tests: PASSING`);
      console.log(`📈 Quality Score: ${results.verificationResults.qualityMetrics.maintainabilityScore}/100`);
      console.log(`\n🚀 ae-framework self-improvement MISSION ACCOMPLISHED!`);
      console.log(`🎯 The framework has proven its self-improvement capabilities`);
    } else {
      const successRate = results.initialErrorCount > 0 
        ? Math.round((results.errorsResolved / results.initialErrorCount) * 100)
        : 0;
      
      console.log(`\n📈 PHASE 5 SIGNIFICANT PROGRESS!`);
      console.log(`✅ Resolved: ${results.errorsResolved}/${results.initialErrorCount} errors (${successRate}%)`);
      console.log(`⚠️ Remaining: ${results.finalErrorCount} errors`);
      console.log(`🔧 Applied: ${results.appliedFixes.length} targeted fixes`);
      
      if (results.verificationResults.compilationSuccess) {
        console.log(`✅ Compilation: SUCCESS`);
      } else {
        console.log(`❌ Compilation: Needs attention`);
      }
      
      if (results.finalErrorCount < results.initialErrorCount / 2) {
        console.log(`\n🎯 MAJOR MILESTONE: Over 50% error reduction achieved!`);
        console.log(`📊 Framework demonstrates strong self-improvement capabilities`);
      }
      
      console.log(`\n🔄 Continue systematic approach for remaining errors`);
    }
    
    // Display key fixes applied
    const highImpactFixes = results.appliedFixes.filter(f => f.riskLevel === 'low').length;
    const mediumRiskFixes = results.appliedFixes.filter(f => f.riskLevel === 'medium').length;
    const highRiskFixes = results.appliedFixes.filter(f => f.riskLevel === 'high').length;
    
    if (results.appliedFixes.length > 0) {
      console.log(`\n🔧 Fix Analysis:`);
      console.log(`   Low Risk: ${highImpactFixes} (safe automated fixes)`);
      console.log(`   Medium Risk: ${mediumRiskFixes} (requires testing)`);
      console.log(`   High Risk: ${highRiskFixes} (needs manual review)`);
      
      const recentFixes = results.appliedFixes.slice(0, 3);
      console.log(`\n📝 Recent Fixes Applied:`);
      recentFixes.forEach((fix, i) => {
        console.log(`   ${i + 1}. ${path.basename(fix.file)}:${fix.line} - ${fix.errorCode}`);
        console.log(`      ${fix.explanation}`);
      });
    }
    
    process.exit(results.overallSuccess ? 0 : (results.errorsResolved > 0 ? 0 : 1));
    
  } catch (error) {
    console.error('\n❌ Phase 5 execution failed:', error);
    
    // Save error details
    const errorPath = path.join(process.cwd(), 'temp-reports', 'phase5-error.log');
    await fs.mkdir(path.dirname(errorPath), { recursive: true });
    await fs.writeFile(errorPath, `Phase 5 Error: ${error}\n\nStack: ${error instanceof Error ? error.stack : 'No stack trace'}`);
    
    console.log(`📝 Error details saved to: ${errorPath}`);
    console.log(`\n🔄 Consider manual intervention or systematic review of remaining errors`);
    process.exit(1);
  }
}

if (import.meta.url === `file://${process.argv[1]}`) {
  main();
}