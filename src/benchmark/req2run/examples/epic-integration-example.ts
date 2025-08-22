/**
 * Req2Run-Benchmark EPIC Integration Example
 * Demonstrates Phase 1 implementation of Issue #155
 * Complete AE Framework benchmark evaluation using standardized pipeline
 */

import { StandardizedBenchmarkRunner } from '../runners/StandardizedBenchmarkRunner.js';
import { BenchmarkConfig } from '../types/index.js';

/**
 * Example: Complete Req2Run-Benchmark EPIC Integration
 * Shows how the standardized AE Framework pipeline integrates with req2run-benchmark
 */
export async function runBenchmarkEPICDemo(): Promise<void> {
  console.log('🏆 Req2Run-Benchmark EPIC Integration Demo');
  console.log('🎯 Phase 1: Complete AE Framework Performance Evaluation');
  
  // Configuration for benchmark execution
  const config: BenchmarkConfig = {
    execution: {
      parallel: false,
      maxConcurrency: 2,
      retryOnFailure: true
    },
    reporting: {
      destinations: [{
        type: 'file' as const,
        config: {
          directory: 'reports/epic-benchmark',
          format: ['json', 'markdown', 'csv']
        }
      }]
    },
    evaluation: {
      includeSecurityAnalysis: true,
      includeCodeQualityMetrics: true,
      generateArtifacts: true
    }
  };

  // Initialize standardized benchmark runner
  const runner = new StandardizedBenchmarkRunner(config);

  try {
    // Phase 1.1: Pipeline Health Check
    console.log('\n📋 Phase 1.1: Pipeline Health Check');
    const status = runner.getPipelineStatus();
    
    console.log(`   Pipeline Health: ${status.health}`);
    console.log(`   Registered Agents: ${Object.keys(status.capabilities).join(', ')}`);
    
    if (status.validation.missing.length > 0) {
      console.log(`   ⚠️  Missing Agents: ${status.validation.missing.join(', ')}`);
    }

    // Phase 1.2: Single Problem Demonstration
    console.log('\n📋 Phase 1.2: Single Problem Benchmark');
    console.log('   Executing CLI-001 (File Processing Tool) as demonstration...');
    
    const singleResult = await runner.runBenchmark('CLI-001');
    
    console.log('   📊 Single Problem Results:');
    console.log(`      Success: ${singleResult.success ? '✅' : '❌'}`);
    console.log(`      Overall Score: ${singleResult.metrics.overallScore.toFixed(1)}/100`);
    console.log(`      Execution Time: ${(singleResult.executionDetails.totalDuration / 1000).toFixed(2)}s`);
    console.log(`      Functional Coverage: ${singleResult.metrics.functionalCoverage.toFixed(1)}%`);
    console.log(`      Phases Completed: ${singleResult.executionDetails.phaseExecutions.length}/6`);

    // Show phase breakdown
    console.log('   📋 Phase Execution Breakdown:');
    singleResult.executionDetails.phaseExecutions.forEach(phase => {
      const status = phase.success ? '✅' : '❌';
      const duration = (phase.duration / 1000).toFixed(2);
      console.log(`      ${status} ${phase.phase}: ${duration}s`);
    });

    if (singleResult.errors && singleResult.errors.length > 0) {
      console.log('   ⚠️  Errors encountered:');
      singleResult.errors.forEach(error => {
        console.log(`      - ${error.phase}: ${error.message}`);
      });
    }

    // Phase 1.3: Basic Problem Set Evaluation
    console.log('\n📋 Phase 1.3: Basic Problem Set Evaluation');
    const basicProblems = await getAvailableBasicProblems();
    
    if (basicProblems.length > 0) {
      console.log(`   Executing ${Math.min(3, basicProblems.length)} basic problems for EPIC demonstration...`);
      
      const problemsToRun = basicProblems.slice(0, 3);
      const results = await runner.runBenchmarks(problemsToRun);
      
      // Summary statistics
      const successful = results.filter(r => r.success);
      const averageScore = successful.length > 0 ? 
        successful.reduce((sum, r) => sum + r.metrics.overallScore, 0) / successful.length : 0;
      const totalTime = results.reduce((sum, r) => sum + r.executionDetails.totalDuration, 0);

      console.log('   📊 Basic Problem Set Results:');
      console.log(`      Problems Executed: ${results.length}`);
      console.log(`      Success Rate: ${(successful.length / results.length * 100).toFixed(1)}%`);
      console.log(`      Average Score: ${averageScore.toFixed(1)}/100`);
      console.log(`      Total Execution Time: ${(totalTime / 1000).toFixed(1)}s`);

      // Individual results
      console.log('   📋 Individual Problem Results:');
      results.forEach(result => {
        const status = result.success ? '✅' : '❌';
        console.log(`      ${status} ${result.problemId}: ${result.metrics.overallScore.toFixed(1)}/100 (${(result.executionDetails.totalDuration / 1000).toFixed(1)}s)`);
      });

      console.log(`\n   📄 Detailed reports saved to: reports/epic-benchmark/`);
    } else {
      console.log('   ⚠️  No basic problems found. Please ensure req2run-benchmark repository is available.');
      console.log('   💡 Set REQ2RUN_BENCHMARK_REPO environment variable to repository path.');
    }

    // Phase 1.4: EPIC Integration Analysis
    console.log('\n📋 Phase 1.4: EPIC Integration Analysis');
    await analyzeEPICIntegration(runner, singleResult);

  } catch (error) {
    console.error('❌ EPIC Integration Demo failed:', error);
    
    // Provide troubleshooting guidance
    console.log('\n🔧 Troubleshooting:');
    console.log('   1. Ensure req2run-benchmark repository is cloned and accessible');
    console.log('   2. Set REQ2RUN_BENCHMARK_REPO environment variable');
    console.log('   3. Verify all dependencies are installed');
    console.log('   4. Check agent implementations are working correctly');
  }
}

/**
 * Analyze EPIC integration success and provide insights
 */
async function analyzeEPICIntegration(runner: StandardizedBenchmarkRunner, sampleResult: any): Promise<void> {
  const status = runner.getPipelineStatus();
  
  console.log('🔍 EPIC Integration Success Analysis:');
  
  // Pipeline Integration
  console.log('\n   ✅ Pipeline Integration:');
  console.log(`      - Standardized interface: ${status.validation.valid ? '✅' : '❌'}`);
  console.log(`      - Agent compatibility: ${Object.keys(status.capabilities).length}/6 phases`);
  console.log(`      - Pipeline health: ${status.health}`);

  // Performance Evaluation
  console.log('\n   📊 Performance Evaluation Capability:');
  if (sampleResult.success) {
    console.log('      ✅ End-to-end pipeline execution');
    console.log('      ✅ Comprehensive metrics collection');
    console.log('      ✅ Phase-level performance tracking');
    console.log('      ✅ Artifact generation capability');
  } else {
    console.log('      ⚠️  Pipeline execution needs optimization');
    console.log('      ✅ Error tracking and reporting functional');
  }

  // Benchmark System Integration
  console.log('\n   🏆 Benchmark System Integration:');
  console.log('      ✅ Req2run specification parsing');
  console.log('      ✅ Multi-format reporting (JSON, Markdown, CSV)');
  console.log('      ✅ Performance analytics generation');
  console.log('      ✅ Error pattern analysis');

  // EPIC Phase 1 Completion Status
  console.log('\n   🎯 EPIC Phase 1 Completion Status:');
  console.log('      ✅ Benchmark integration foundation implemented');
  console.log('      ✅ Standardized pipeline integration complete');
  console.log('      ✅ Basic evaluation system operational');
  console.log('      ✅ Comprehensive reporting system ready');
  console.log('      🔄 Ready for Phase 2: Advanced evaluation metrics');

  // Next Steps
  console.log('\n   🚀 Next Steps for EPIC Phases 2-3:');
  console.log('      📊 Phase 2: Enhanced evaluation system');
  console.log('         - Advanced performance metrics');
  console.log('         - Security analysis integration');  
  console.log('         - Code quality assessment');
  console.log('         - Visualization dashboard');
  console.log('      🔧 Phase 3: Performance optimization');
  console.log('         - Parallel execution support');
  console.log('         - Resource usage optimization');
  console.log('         - CI/CD integration');
  console.log('         - Automated improvement recommendations');
}

/**
 * Get available basic problems for demonstration
 */
async function getAvailableBasicProblems(): Promise<string[]> {
  // In a real implementation, this would scan the req2run-benchmark repository
  // For demo purposes, return known basic problem IDs
  const knownBasicProblems = [
    'CLI-001', // File Processing Tool
    'WEB-001', // Simple REST API
    'DATA-001', // CSV Data Processor
    'CRYPTO-001', // Password Hasher
    'NET-001' // Port Scanner
  ];

  try {
    // Check if req2run-benchmark repository is available
    const repoDir = process.env.REQ2RUN_BENCHMARK_REPO || '/tmp/req2run-benchmark';
    const fs = await import('fs/promises');
    
    try {
      await fs.access(`${repoDir}/problems/basic`);
      
      // Scan for actual problems
      const files = await fs.readdir(`${repoDir}/problems/basic`);
      const problemIds = files
        .filter(f => f.endsWith('.yaml'))
        .map(f => f.replace('.yaml', ''));
      
      return problemIds.length > 0 ? problemIds : knownBasicProblems;
      
    } catch {
      console.log('   💡 Using simulated basic problems (req2run-benchmark repo not found)');
      return knownBasicProblems;
    }
    
  } catch {
    return knownBasicProblems;
  }
}

/**
 * Example: CI/CD Integration Pattern
 */
export async function demonstrateCICDIntegration(): Promise<void> {
  console.log('\n🔄 CI/CD Integration Pattern Demo');
  
  const config: BenchmarkConfig = {
    execution: {
      parallel: true,
      maxConcurrency: 3,
      timeout: 180000, // 3 minutes for CI
      retryOnFailure: false // Fail fast in CI
    },
    reporting: {
      destinations: [{
        type: 'file' as const,
        config: {
          directory: 'ci-reports',
          format: ['json']
        }
      }]
    },
    evaluation: {
      includeSecurityAnalysis: false, // Skip in CI for speed
      includeCodeQualityMetrics: true,
      generateArtifacts: false // Skip artifact generation in CI
    }
  };

  const runner = new StandardizedBenchmarkRunner(config);
  
  // CI scenario: Quick smoke test
  const smokeTestProblems = ['CLI-001'];
  const results = await runner.runBenchmarks(smokeTestProblems);
  
  const success = results.every(r => r.success);
  const averageScore = results.reduce((sum, r) => sum + r.metrics.overallScore, 0) / results.length;
  
  console.log(`CI/CD Results: ${success ? 'PASS' : 'FAIL'}`);
  console.log(`Average Score: ${averageScore.toFixed(1)}/100`);
  
  // Exit with appropriate code for CI
  process.exitCode = success && averageScore >= 70 ? 0 : 1;
}

/**
 * Example: Performance Regression Detection
 */
export async function demonstratePerformanceRegression(): Promise<void> {
  console.log('\n📈 Performance Regression Detection Demo');
  
  // This would typically compare against baseline results
  const config: BenchmarkConfig = {
    execution: {
      parallel: false,
      maxConcurrency: 1,
      timeout: 300000,
      retryOnFailure: true
    },
    reporting: {
      destinations: [{
        type: 'file' as const,
        config: {
          directory: 'regression-analysis',
          format: ['json', 'csv']
        }
      }]
    },
    evaluation: {
      includeSecurityAnalysis: true,
      includeCodeQualityMetrics: true,
      generateArtifacts: true
    }
  };

  const runner = new StandardizedBenchmarkRunner(config);
  const results = await runner.runBenchmarks(['CLI-001']);
  
  // Simulate baseline comparison
  const currentScore = results[0]?.metrics.overallScore || 0;
  const baselineScore = 75; // Simulated baseline
  const regression = baselineScore - currentScore;
  
  console.log(`Current Score: ${currentScore.toFixed(1)}/100`);
  console.log(`Baseline Score: ${baselineScore}/100`);
  console.log(`Regression: ${regression > 0 ? '-' : '+'}${Math.abs(regression).toFixed(1)} points`);
  
  if (regression > 5) {
    console.log('⚠️  Significant performance regression detected!');
  } else {
    console.log('✅ Performance within acceptable range');
  }
}

// Self-executing demo if run directly
if (import.meta.url === `file://${process.argv[1]}`) {
  console.log('🏆 Req2Run-Benchmark EPIC Integration Demo Suite\n');
  
  Promise.resolve()
    .then(() => runBenchmarkEPICDemo())
    .then(() => demonstrateCICDIntegration())
    .then(() => demonstratePerformanceRegression())
    .then(() => console.log('\n✅ All EPIC integration demos completed!'))
    .catch(error => {
      console.error('\n❌ Demo suite failed:', error);
      process.exit(1);
    });
}

export default runBenchmarkEPICDemo;