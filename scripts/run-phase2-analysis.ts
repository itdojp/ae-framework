#!/usr/bin/env npx tsx

/**
 * Script to run Phase 2 Natural Language Requirements Analysis
 */

import { Phase2RequirementsAnalyzer } from '../src/self-improvement/phase2-requirements-analysis.js';
import * as fs from 'fs/promises';
import * as path from 'path';

async function main() {
  console.log('🔍 Starting ae-framework Phase 2 Natural Language Requirements Analysis...\n');
  
  const analyzer = new Phase2RequirementsAnalyzer();
  
  try {
    console.log('🧠 Analyzing TypeScript error resolution requirements...');
    console.log('🏗️ Analyzing framework architectural requirements...');
    console.log('📐 Analyzing architectural improvement requirements...');
    console.log('📊 Creating prioritized action plan...\n');
    
    const results = await analyzer.analyzeRequirements();
    const report = analyzer.generateReport(results);
    
    // Output to console
    console.log(report);
    
    // Save report to file
    const reportPath = path.join(process.cwd(), 'temp-reports', 'phase2-requirements-analysis.md');
    await fs.mkdir(path.dirname(reportPath), { recursive: true });
    await fs.writeFile(reportPath, report);
    
    console.log(`\n📄 Requirements analysis saved to: ${reportPath}`);
    
    // Output systematic plan summary
    console.log('\n📋 Systematic Implementation Plan Summary:');
    results.systematicPlan.forEach((phase, index) => {
      console.log(`\n${index + 1}. ${phase.phase}`);
      console.log(`   ${phase.description}`);
      console.log(`   Tasks: ${phase.tasks.length}`);
      console.log(`   Outcome: ${phase.expectedOutcome}`);
    });
    
    // Output priority counts
    console.log('\n🎯 Priority Distribution:');
    console.log(`   High Priority: ${results.prioritizedActions.high.length} items`);
    console.log(`   Medium Priority: ${results.prioritizedActions.medium.length} items`);
    console.log(`   Low Priority: ${results.prioritizedActions.low.length} items`);
    
    console.log('\n✅ Phase 2 Natural Language Requirements Analysis complete!');
    process.exit(0);
    
  } catch (error) {
    console.error('❌ Analysis failed:', error);
    process.exit(1);
  }
}

if (import.meta.url === `file://${process.argv[1]}`) {
  main();
}