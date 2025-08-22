#!/usr/bin/env npx tsx

/**
 * Script to execute Phase 3: Formal Specification & Testing
 */

import { Phase3FormalTesting } from '../src/self-improvement/phase3-formal-testing.js';
import * as fs from 'fs/promises';
import * as path from 'path';

async function main() {
  console.log('🚀 Starting ae-framework Phase 3: Formal Specification & Testing...\n');
  
  const phase3 = new Phase3FormalTesting();
  
  try {
    const startTime = Date.now();
    
    console.log('📊 Executing formal specification and testing phase...');
    const results = await phase3.executePhase3();
    
    const endTime = Date.now();
    const duration = Math.round((endTime - startTime) / 1000);
    
    // Generate and display report
    const report = phase3.generatePhase3Report(results);
    console.log(report);
    
    // Save detailed results to file
    const reportPath = path.join(process.cwd(), 'temp-reports', 'phase3-formal-testing.md');
    await fs.mkdir(path.dirname(reportPath), { recursive: true });
    await fs.writeFile(reportPath, report);
    
    // Save detailed results as JSON
    const resultsPath = path.join(process.cwd(), 'temp-reports', 'phase3-results.json');
    await fs.writeFile(resultsPath, JSON.stringify(results, null, 2));
    
    console.log(`\n📄 Phase 3 report saved to: ${reportPath}`);
    console.log(`📊 Detailed results saved to: ${resultsPath}`);
    console.log(`⏱️ Phase 3 completed in ${duration} seconds`);
    
    // Summary output
    console.log('\n📋 Phase 3 Summary:');
    console.log(`   Formal Specifications: 3 generated`);
    console.log(`   Tests Generated: ${
      results.generatedTests.unitTests.length + 
      results.generatedTests.integrationTests.length + 
      results.generatedTests.typeValidationTests.length
    }`);
    console.log(`   Validation: ${results.validationResults.specificationCompliance ? 'PASSED' : 'FAILED'}`);
    console.log(`   Quality Score: ${results.validationResults.qualityScore}/100`);
    
    if (results.validationResults.errors.length > 0) {
      console.log(`\n❌ Errors found: ${results.validationResults.errors.length}`);
      results.validationResults.errors.forEach(error => {
        console.log(`   - ${error}`);
      });
    }
    
    if (results.validationResults.warnings.length > 0) {
      console.log(`\n⚠️ Warnings: ${results.validationResults.warnings.length}`);
      results.validationResults.warnings.slice(0, 3).forEach(warning => {
        console.log(`   - ${warning}`);
      });
      if (results.validationResults.warnings.length > 3) {
        console.log(`   ... and ${results.validationResults.warnings.length - 3} more warnings`);
      }
    }
    
    console.log('\n✅ Phase 3 Formal Specification & Testing completed!');
    
    // Determine success based on results
    const success = results.validationResults.specificationCompliance && 
                   results.validationResults.qualityScore >= 70;
    
    if (success) {
      console.log('🎯 Phase 3 SUCCESS: Ready to proceed to Phase 4 (Code Generation)');
    } else {
      console.log('🔄 Phase 3 NEEDS IMPROVEMENT: Review errors and warnings before proceeding');
    }
    
    process.exit(success ? 0 : 1);
    
  } catch (error) {
    console.error('❌ Phase 3 execution failed:', error);
    
    // Save error details
    const errorPath = path.join(process.cwd(), 'temp-reports', 'phase3-error.log');
    await fs.mkdir(path.dirname(errorPath), { recursive: true });
    await fs.writeFile(errorPath, `Phase 3 Error: ${error}\n\nStack: ${error.stack}`);
    
    console.log(`📝 Error details saved to: ${errorPath}`);
    process.exit(1);
  }
}

if (import.meta.url === `file://${process.argv[1]}`) {
  main();
}