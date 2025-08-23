#!/usr/bin/env node

/**
 * Enhanced Flake Detector
 * Advanced flaky test detection with pattern analysis and early warning
 */

import { spawn } from 'child_process';
import fs from 'fs';
import path from 'path';
import { glob } from 'glob';

class EnhancedFlakeDetector {
  constructor(options = {}) {
    this.runs = options.runs || 15;
    this.threshold = options.threshold || 0.05; // 5% failure rate
    this.earlyWarningThreshold = options.earlyWarningThreshold || 0.15; // 15% for warnings
    this.testPattern = options.testPattern || 'tests/**/*.test.ts';
    this.outputDir = options.outputDir || './reports/flake-detection';
    this.results = new Map();
    this.testPatterns = new Map();
    this.failureAnalysis = new Map();
    this.executionMetrics = new Map();
    this.config = this.loadConfig();
  }

  loadConfig() {
    try {
      const configPath = './config/flake-detection.json';
      if (fs.existsSync(configPath)) {
        return JSON.parse(fs.readFileSync(configPath, 'utf8'));
      }
    } catch (error) {
      console.warn(`Warning: Could not load flake detection config: ${error.message}`);
    }

    return {
      patterns: {
        timeoutKeywords: ['timeout', 'timed out', 'exceeded', 'hang'],
        resourceKeywords: ['memory', 'leak', 'handle', 'worker', 'process'],
        concurrencyKeywords: ['race', 'concurrent', 'parallel', 'async'],
        environmentKeywords: ['CI', 'environment', 'platform', 'node_modules']
      },
      analysis: {
        minimumRuns: 5,
        confidenceInterval: 0.95,
        trendAnalysisWindow: 10
      },
      alerts: {
        githubIssue: true,
        slackNotification: false,
        emailAlert: false
      }
    };
  }

  async runTestSuite(run, testFile = null) {
    return new Promise((resolve, reject) => {
      const startTime = Date.now();
      const testCommand = testFile ? 
        ['npx', 'vitest', 'run', testFile, '--reporter=verbose'] :
        ['pnpm', 'test:fast'];
      
      console.log(`🔄 Running test suite (${run}/${this.runs})${testFile ? ` - ${testFile}` : ''}...`);
      
      const testProcess = spawn(testCommand[0], testCommand.slice(1), {
        stdio: ['inherit', 'pipe', 'pipe'],
        timeout: 120000 // 2 minute timeout
      });

      // Additional timeout protection
      const forceTimeout = setTimeout(() => {
        console.log(`   ⏰ Force killing test process after 2.5 minutes`);
        testProcess.kill('SIGKILL');
      }, 150000);

      let stdout = '';
      let stderr = '';

      testProcess.stdout?.on('data', (data) => {
        stdout += data.toString();
      });

      testProcess.stderr?.on('data', (data) => {
        stderr += data.toString();
      });

      testProcess.on('close', (code) => {
        const duration = Date.now() - startTime;
        clearTimeout(forceTimeout);
        
        resolve({
          run,
          success: code === 0,
          exitCode: code,
          stdout,
          stderr,
          duration,
          timestamp: new Date().toISOString(),
          testFile: testFile || 'all'
        });
      });

      testProcess.on('error', (error) => {
        clearTimeout(forceTimeout);
        reject({
          run,
          success: false,
          error: error.message,
          timestamp: new Date().toISOString(),
          testFile: testFile || 'all'
        });
      });
    });
  }

  analyzeFailurePatterns(result) {
    const patterns = this.config.patterns;
    const analysis = {
      failureType: 'unknown',
      keywords: [],
      severity: 'low',
      suggestedActions: []
    };

    const combinedOutput = `${result.stdout} ${result.stderr}`.toLowerCase();

    // Analyze failure patterns
    for (const [category, keywords] of Object.entries(patterns)) {
      const matchedKeywords = keywords.filter(keyword => 
        combinedOutput.includes(keyword.toLowerCase())
      );
      
      if (matchedKeywords.length > 0) {
        analysis.keywords.push(...matchedKeywords);
        
        switch (category) {
          case 'timeoutKeywords':
            analysis.failureType = 'timeout';
            analysis.severity = 'high';
            analysis.suggestedActions.push('Increase test timeouts');
            analysis.suggestedActions.push('Check for infinite loops or hanging operations');
            break;
          case 'resourceKeywords':
            analysis.failureType = 'resource';
            analysis.severity = 'high';
            analysis.suggestedActions.push('Investigate resource leaks');
            analysis.suggestedActions.push('Improve cleanup in afterEach hooks');
            break;
          case 'concurrencyKeywords':
            analysis.failureType = 'concurrency';
            analysis.severity = 'medium';
            analysis.suggestedActions.push('Review async/await usage');
            analysis.suggestedActions.push('Check for race conditions');
            break;
          case 'environmentKeywords':
            analysis.failureType = 'environment';
            analysis.severity = 'medium';
            analysis.suggestedActions.push('Investigate CI-specific issues');
            analysis.suggestedActions.push('Check environment dependencies');
            break;
        }
      }
    }

    // Duration analysis
    if (result.duration > 120000) { // > 2 minutes
      analysis.keywords.push('slow execution');
      analysis.suggestedActions.push('Optimize test performance');
    }

    return analysis;
  }

  calculateStatistics(testResults) {
    const total = testResults.length;
    const failures = testResults.filter(r => !r.success).length;
    const failureRate = failures / total;
    
    // Calculate confidence interval
    const z = 1.96; // 95% confidence
    const margin = z * Math.sqrt((failureRate * (1 - failureRate)) / total);
    
    return {
      total,
      failures,
      successes: total - failures,
      failureRate,
      confidenceInterval: {
        lower: Math.max(0, failureRate - margin),
        upper: Math.min(1, failureRate + margin)
      },
      averageDuration: testResults.reduce((sum, r) => sum + (r.duration || 0), 0) / total,
      classification: this.classifyStability(failureRate)
    };
  }

  classifyStability(failureRate) {
    if (failureRate === 0) return 'stable';
    if (failureRate < this.threshold) return 'minor-instability';
    if (failureRate < this.earlyWarningThreshold) return 'flaky-warning';
    if (failureRate < 0.5) return 'highly-flaky';
    return 'consistently-failing';
  }

  async detectFlakeTests() {
    console.log('🔍 Starting enhanced flake detection...');
    console.log(`   Runs: ${this.runs}`);
    console.log(`   Threshold: ${(this.threshold * 100).toFixed(1)}%`);
    console.log(`   Early Warning: ${(this.earlyWarningThreshold * 100).toFixed(1)}%`);

    const allResults = [];
    
    // Run test suite multiple times
    for (let run = 1; run <= this.runs; run++) {
      try {
        const result = await this.runTestSuite(run);
        allResults.push(result);
        
        // Early failure analysis
        if (!result.success) {
          const analysis = this.analyzeFailurePatterns(result);
          console.log(`   ⚠️  Run ${run} failed: ${analysis.failureType} (${analysis.severity})`);
          
          if (analysis.keywords.length > 0) {
            console.log(`      Keywords: ${analysis.keywords.join(', ')}`);
          }
        }
        
        // Early termination if clearly stable
        if (run >= 5) {
          const recentFailures = allResults.slice(-5).filter(r => !r.success).length;
          if (recentFailures === 0 && run >= 8) {
            console.log(`   ✅ Early termination: Tests appear stable after ${run} runs`);
            break;
          }
        }
        
      } catch (error) {
        console.error(`   ❌ Run ${run} errored:`, error.error || error.message);
        allResults.push(error);
      }
    }

    // Analyze results
    const statistics = this.calculateStatistics(allResults);
    const failedResults = allResults.filter(r => !r.success);
    
    // Pattern analysis for failures
    const patternAnalysis = {
      commonFailures: new Map(),
      failureCategories: new Map(),
      timeDistribution: []
    };

    failedResults.forEach(result => {
      const analysis = this.analyzeFailurePatterns(result);
      
      // Count failure types
      const category = analysis.failureType;
      patternAnalysis.failureCategories.set(
        category, 
        (patternAnalysis.failureCategories.get(category) || 0) + 1
      );
      
      // Track timing
      patternAnalysis.timeDistribution.push(result.duration || 0);
    });

    return {
      statistics,
      patternAnalysis,
      results: allResults,
      recommendation: this.generateRecommendation(statistics, patternAnalysis)
    };
  }

  generateRecommendation(statistics, patternAnalysis) {
    const recommendations = [];
    const { classification, failureRate } = statistics;
    
    switch (classification) {
      case 'stable':
        recommendations.push('✅ Tests are stable - no action required');
        break;
      case 'minor-instability':
        recommendations.push('⚠️ Minor instability detected - monitor for trends');
        recommendations.push('Consider increasing test isolation');
        break;
      case 'flaky-warning':
        recommendations.push('🟡 Early warning - investigate before CI failures');
        recommendations.push('Review recent changes that might affect test stability');
        break;
      case 'highly-flaky':
        recommendations.push('🔴 Highly flaky tests detected - immediate action required');
        recommendations.push('Consider isolating these tests from CI');
        break;
      case 'consistently-failing':
        recommendations.push('❌ Tests consistently failing - likely real bugs');
        recommendations.push('Fix underlying issues before addressing flakiness');
        break;
    }

    // Pattern-specific recommendations
    const topFailureType = Array.from(patternAnalysis.failureCategories.entries())
      .sort((a, b) => b[1] - a[1])[0];
      
    if (topFailureType) {
      const [type, count] = topFailureType;
      recommendations.push(`Most common failure type: ${type} (${count} occurrences)`);
      
      switch (type) {
        case 'timeout':
          recommendations.push('• Increase test timeouts in CI configuration');
          recommendations.push('• Review async operations for proper completion');
          break;
        case 'resource':
          recommendations.push('• Improve resource cleanup in test teardown');
          recommendations.push('• Check for memory leaks with --expose-gc');
          break;
        case 'concurrency':
          recommendations.push('• Reduce test parallelism');
          recommendations.push('• Add proper synchronization for shared resources');
          break;
        case 'environment':
          recommendations.push('• Review CI environment differences');
          recommendations.push('• Check for missing dependencies or configurations');
          break;
      }
    }

    return recommendations;
  }

  async generateReport(detectionResults) {
    const { statistics, patternAnalysis, results, recommendation } = detectionResults;
    
    const report = {
      summary: {
        testSuiteRuns: results.length,
        failureRate: `${(statistics.failureRate * 100).toFixed(2)}%`,
        classification: statistics.classification,
        confidence: `${(this.config.analysis.confidenceInterval * 100)}%`,
        generatedAt: new Date().toISOString()
      },
      statistics,
      patternAnalysis: {
        failureCategories: Object.fromEntries(patternAnalysis.failureCategories),
        averageFailureDuration: patternAnalysis.timeDistribution.length > 0 ?
          patternAnalysis.timeDistribution.reduce((a, b) => a + b, 0) / patternAnalysis.timeDistribution.length :
          0
      },
      recommendations: recommendation,
      results: results.map(r => ({
        run: r.run,
        success: r.success,
        duration: r.duration,
        timestamp: r.timestamp,
        exitCode: r.exitCode
      }))
    };

    // Save report
    if (!fs.existsSync(this.outputDir)) {
      fs.mkdirSync(this.outputDir, { recursive: true });
    }
    
    const reportPath = path.join(this.outputDir, `flake-detection-${Date.now()}.json`);
    fs.writeFileSync(reportPath, JSON.stringify(report, null, 2));
    
    // Display summary
    console.log('\n📊 Flake Detection Results:');
    console.log(`   Classification: ${statistics.classification}`);
    console.log(`   Failure Rate: ${(statistics.failureRate * 100).toFixed(2)}%`);
    console.log(`   Confidence Interval: ${(statistics.confidenceInterval.lower * 100).toFixed(1)}% - ${(statistics.confidenceInterval.upper * 100).toFixed(1)}%`);
    
    if (patternAnalysis.failureCategories.size > 0) {
      console.log('\n🔍 Failure Patterns:');
      Array.from(patternAnalysis.failureCategories.entries())
        .sort((a, b) => b[1] - a[1])
        .forEach(([type, count]) => {
          console.log(`   • ${type}: ${count} occurrences`);
        });
    }
    
    console.log('\n💡 Recommendations:');
    recommendation.forEach(rec => {
      console.log(`   ${rec}`);
    });
    
    console.log(`\n📄 Full report saved: ${reportPath}`);
    
    // Auto-create GitHub issue if highly flaky
    if (statistics.classification === 'highly-flaky' && this.config.alerts.githubIssue) {
      await this.createGitHubIssue(report);
    }
    
    return report;
  }

  async createGitHubIssue(report) {
    console.log('🚨 Creating GitHub issue for highly flaky tests...');
    
    const issueBody = `## 🚨 Flaky Test Alert

**Detection Time:** ${report.summary.generatedAt}
**Failure Rate:** ${report.summary.failureRate}
**Classification:** ${report.summary.classification}

### 📊 Statistics
- Total Runs: ${report.summary.testSuiteRuns}
- Failed Runs: ${report.statistics.failures}
- Success Runs: ${report.statistics.successes}

### 🔍 Pattern Analysis
${Object.entries(report.patternAnalysis.failureCategories)
  .map(([type, count]) => `- **${type}**: ${count} occurrences`)
  .join('\n')}

### 💡 Recommendations
${report.recommendations.map(rec => `- ${rec}`).join('\n')}

**Auto-generated by Enhanced Flake Detector**`;

    try {
      // This would integrate with GitHub API
      console.log('   📝 Issue content prepared');
      console.log('   🔗 Integration with GitHub API would create issue here');
      return true;
    } catch (error) {
      console.error('   ❌ Failed to create GitHub issue:', error.message);
      return false;
    }
  }
}

// CLI Interface
async function main() {
  const args = process.argv.slice(2);
  const options = {};
  
  // Parse command line arguments
  for (let i = 0; i < args.length; i += 2) {
    const key = args[i].replace('--', '');
    const value = args[i + 1];
    
    switch (key) {
      case 'runs':
        options.runs = parseInt(value);
        break;
      case 'threshold':
        options.threshold = parseFloat(value);
        break;
      case 'pattern':
        options.testPattern = value;
        break;
      case 'output':
        options.outputDir = value;
        break;
    }
  }
  
  const detector = new EnhancedFlakeDetector(options);
  
  try {
    const results = await detector.detectFlakeTests();
    await detector.generateReport(results);
  } catch (error) {
    console.error('❌ Flake detection failed:', error.message);
    process.exit(1);
  }
}

if (import.meta.url === `file://${process.argv[1]}`) {
  main();
}

export { EnhancedFlakeDetector };