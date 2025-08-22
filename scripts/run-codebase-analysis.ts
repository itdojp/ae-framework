#!/usr/bin/env tsx

/**
 * Script to run Phase 1 codebase analysis using NaturalLanguageTaskAdapter
 */

import { CodebaseAnalyzer } from '../src/self-improvement/codebase-analysis.js';
import * as fs from 'fs/promises';
import * as path from 'path';

async function main() {
  console.log('🔍 Starting ae-framework Phase 1 Codebase Analysis...\n');
  
  const analyzer = new CodebaseAnalyzer();
  
  try {
    const results = await analyzer.analyzeCodebase();
    const report = analyzer.generateReport(results);
    
    // Output to console
    console.log(report);
    
    // Save report to file
    const reportPath = path.join(process.cwd(), 'temp-reports', 'phase1-codebase-analysis.md');
    await fs.mkdir(path.dirname(reportPath), { recursive: true });
    await fs.writeFile(reportPath, report);
    
    console.log(`\n📄 Report saved to: ${reportPath}`);
    
    // Exit with appropriate code
    process.exit(results.shouldBlockProgress ? 1 : 0);
    
  } catch (error) {
    console.error('❌ Analysis failed:', error);
    process.exit(1);
  }
}

if (import.meta.url === `file://${process.argv[1]}`) {
  main();
}