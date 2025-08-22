#!/usr/bin/env npx tsx

/**
 * Script to execute Phase 3 Simple Implementation
 */

import { Phase3Simple } from '../src/self-improvement/phase3-simple.js';
import * as fs from 'fs/promises';
import * as path from 'path';

async function main() {
  console.log('🚀 Starting ae-framework Phase 3 Simple Implementation...\n');
  
  const phase3 = new Phase3Simple();
  
  try {
    const startTime = Date.now();
    const results = await phase3.executeSimplePhase3();
    const endTime = Date.now();
    const duration = Math.round((endTime - startTime) / 1000);
    
    // Generate and display report
    const report = phase3.generateSimpleReport(results);
    console.log('\n' + report);
    
    // Save report
    const reportPath = path.join(process.cwd(), 'temp-reports', 'phase3-simple.md');
    await fs.mkdir(path.dirname(reportPath), { recursive: true });
    await fs.writeFile(reportPath, report);
    
    console.log(`\n📄 Report saved to: ${reportPath}`);
    console.log(`⏱️ Completed in ${duration} seconds`);
    
    if (results.success) {
      console.log('\n✅ Phase 3 Simple: SUCCESS - Ready for systematic TypeScript error resolution');
    } else {
      console.log('\n❌ Phase 3 Simple: FAILED - Check errors above');
    }
    
    process.exit(results.success ? 0 : 1);
    
  } catch (error) {
    console.error('\n❌ Phase 3 Simple execution failed:', error);
    process.exit(1);
  }
}

if (import.meta.url === `file://${process.argv[1]}`) {
  main();
}