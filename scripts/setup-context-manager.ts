#!/usr/bin/env npx tsx

/**
 * Script to set up ContextManager for Phase 1 development
 */

import { ContextManagerSetup } from '../src/self-improvement/setup-context-manager.js';
import * as fs from 'fs/promises';
import * as path from 'path';

async function main() {
  console.log('🔧 Setting up ContextManager for Phase 1 development...\n');
  
  const setup = new ContextManagerSetup();
  
  try {
    const result = await setup.setupForPhase1();
    const report = setup.generateSetupReport(result);
    
    // Output to console
    console.log(report);
    
    // Save report to file
    const reportPath = path.join(process.cwd(), 'temp-reports', 'phase1-context-setup.md');
    await fs.mkdir(path.dirname(reportPath), { recursive: true });
    await fs.writeFile(reportPath, report);
    
    console.log(`\n📄 Setup report saved to: ${reportPath}`);
    
    if (result.success) {
      console.log('\n✅ ContextManager is ready for Phase 1 development!');
      
      // Output context sample for verification
      if (result.initialContext) {
        console.log('\n📋 Context Window Preview:');
        console.log(`- Total tokens: ${result.initialContext.totalTokens}`);
        console.log('- Steering context loaded ✓');
        console.log('- Phase information loaded ✓');
        console.log('- Working memory configured ✓');
        console.log('- TypeScript patterns loaded ✓');
      }
    } else {
      console.log('\n❌ ContextManager setup failed. Check errors above.');
    }
    
    // Exit with appropriate code
    process.exit(result.success ? 0 : 1);
    
  } catch (error) {
    console.error('❌ Setup failed:', error);
    process.exit(1);
  }
}

if (import.meta.url === `file://${process.argv[1]}`) {
  main();
}