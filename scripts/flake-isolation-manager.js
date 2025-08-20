#!/usr/bin/env node

/**
 * Flake Isolation Manager
 * Automatically isolates flaky tests and manages their lifecycle
 */

const fs = require('fs');
const path = require('path');
const { execSync } = require('child_process');

class FlakeIsolationManager {
  constructor() {
    this.flakeConfigPath = './config/flaky-tests.json';
    this.testPatternsPath = './config/test-patterns.json';
    this.reportsPath = './reports/flake-reports';
    this.config = this.loadFlakeConfig();
  }

  loadFlakeConfig() {
    try {
      if (fs.existsSync(this.flakeConfigPath)) {
        return JSON.parse(fs.readFileSync(this.flakeConfigPath, 'utf8'));
      }
    } catch (error) {
      console.warn(`Warning: Could not load flake config: ${error.message}`);
    }
    
    return {
      isolatedTests: [],
      thresholds: {
        isolationThreshold: 0.3,    // 30% failure rate triggers isolation
        recoveryThreshold: 0.05,    // 5% failure rate allows recovery
        minRunsForIsolation: 5,     // Minimum runs before isolation
        minRunsForRecovery: 10      // Minimum runs before recovery
      },
      retryPolicy: {
        maxRetries: 3,
        retryDelay: 1000,
        exponentialBackoff: true
      },
      notifications: {
        slack: false,
        email: false,
        github: true
      }
    };
  }

  saveFlakeConfig() {
    const configDir = path.dirname(this.flakeConfigPath);
    if (!fs.existsSync(configDir)) {
      fs.mkdirSync(configDir, { recursive: true });
    }
    fs.writeFileSync(this.flakeConfigPath, JSON.stringify(this.config, null, 2));
  }

  generateTestPatternConfig() {
    const testPatterns = {
      stable: {
        include: [
          "tests/unit/**/*.test.ts",
          "tests/property/**/*.test.ts"
        ],
        exclude: this.config.isolatedTests.map(test => test.pattern)
      },
      integration: {
        include: [
          "tests/integration/**/*.test.ts",
          "tests/optimization/system-integration.test.ts"
        ],
        exclude: this.config.isolatedTests
          .filter(test => test.category === 'integration')
          .map(test => test.pattern)
      },
      performance: {
        include: [
          "tests/optimization/performance-benchmarks.test.ts",
          "tests/perf/**/*.test.ts"
        ],
        exclude: this.config.isolatedTests
          .filter(test => test.category === 'performance')
          .map(test => test.pattern)
      },
      isolated: {
        include: this.config.isolatedTests
          .filter(test => test.status === 'isolated')
          .map(test => test.pattern),
        exclude: []
      }
    };

    const patternsDir = path.dirname(this.testPatternsPath);
    if (!fs.existsSync(patternsDir)) {
      fs.mkdirSync(patternsDir, { recursive: true });
    }
    fs.writeFileSync(this.testPatternsPath, JSON.stringify(testPatterns, null, 2));
    
    console.log(`📝 Updated test patterns configuration: ${this.testPatternsPath}`);
  }

  isolateTest(testPattern, metadata = {}) {
    const existingTest = this.config.isolatedTests.find(test => test.pattern === testPattern);
    
    if (existingTest) {
      existingTest.isolatedAt = new Date().toISOString();
      existingTest.isolationCount = (existingTest.isolationCount || 0) + 1;
      existingTest.metadata = { ...existingTest.metadata, ...metadata };
      console.log(`🔒 Re-isolated test: ${testPattern} (count: ${existingTest.isolationCount})`);
    } else {
      const newIsolatedTest = {
        pattern: testPattern,
        status: 'isolated',
        isolatedAt: new Date().toISOString(),
        isolationCount: 1,
        category: this.detectTestCategory(testPattern),
        metadata: {
          failureRate: metadata.failureRate || 'unknown',
          lastSeen: metadata.lastSeen || new Date().toISOString(),
          reason: metadata.reason || 'flaky-behavior',
          ...metadata
        },
        recovery: {
          attempts: 0,
          lastAttempt: null,
          successfulRuns: 0,
          totalRuns: 0
        }
      };
      
      this.config.isolatedTests.push(newIsolatedTest);
      console.log(`🚫 Isolated new flaky test: ${testPattern}`);
    }
    
    this.saveFlakeConfig();
    this.generateTestPatternConfig();
    this.generateFlakeReport();
  }

  detectTestCategory(testPattern) {
    if (testPattern.includes('integration') || testPattern.includes('system-integration')) {
      return 'integration';
    } else if (testPattern.includes('performance') || testPattern.includes('perf')) {
      return 'performance';
    } else if (testPattern.includes('unit')) {
      return 'unit';
    } else if (testPattern.includes('e2e')) {
      return 'e2e';
    }
    return 'unknown';
  }

  async tryRecoverTest(testPattern, runs = 10) {
    console.log(`🔄 Attempting recovery for test: ${testPattern} (${runs} runs)`);
    
    const test = this.config.isolatedTests.find(t => t.pattern === testPattern);
    if (!test) {
      console.error(`❌ Test not found in isolated list: ${testPattern}`);
      return false;
    }

    let successCount = 0;
    let totalRuns = 0;

    try {
      for (let i = 0; i < runs; i++) {
        console.log(`  🧪 Recovery run ${i + 1}/${runs}`);
        
        try {
          // Run the specific test pattern
          execSync(`npm test -- --testPathPattern="${testPattern.replace(/\*/g, '.*')}"`, {
            stdio: 'pipe',
            timeout: 60000 // 1 minute timeout
          });
          successCount++;
          console.log(`    ✅ Run ${i + 1} passed`);
        } catch (error) {
          console.log(`    ❌ Run ${i + 1} failed`);
        }
        
        totalRuns++;
        
        // Brief pause between runs
        await new Promise(resolve => setTimeout(resolve, 1000));
      }
      
      const successRate = successCount / totalRuns;
      console.log(`📊 Recovery results: ${successCount}/${totalRuns} (${Math.round(successRate * 100)}% success)`);
      
      // Update test recovery data
      test.recovery.attempts++;
      test.recovery.lastAttempt = new Date().toISOString();
      test.recovery.successfulRuns += successCount;
      test.recovery.totalRuns += totalRuns;
      
      // Check if test meets recovery criteria
      if (successRate >= (1 - this.config.thresholds.recoveryThreshold) && totalRuns >= this.config.thresholds.minRunsForRecovery) {
        test.status = 'recovered';
        test.recoveredAt = new Date().toISOString();
        
        console.log(`🎉 Test recovered successfully: ${testPattern}`);
        
        this.saveFlakeConfig();
        this.generateTestPatternConfig();
        return true;
      } else {
        console.log(`⏳ Test not yet ready for recovery: ${testPattern} (${Math.round(successRate * 100)}% success rate)`);
        
        this.saveFlakeConfig();
        return false;
      }
    } catch (error) {
      console.error(`❌ Recovery attempt failed: ${error.message}`);
      return false;
    }
  }

  removeTest(testPattern) {
    const initialLength = this.config.isolatedTests.length;
    this.config.isolatedTests = this.config.isolatedTests.filter(test => test.pattern !== testPattern);
    
    if (this.config.isolatedTests.length < initialLength) {
      console.log(`🗑️  Removed test from isolation: ${testPattern}`);
      this.saveFlakeConfig();
      this.generateTestPatternConfig();
      return true;
    } else {
      console.log(`⚠️  Test not found in isolation list: ${testPattern}`);
      return false;
    }
  }

  generateFlakeReport() {
    if (!fs.existsSync(this.reportsPath)) {
      fs.mkdirSync(this.reportsPath, { recursive: true });
    }

    const report = {
      timestamp: new Date().toISOString(),
      summary: {
        totalIsolated: this.config.isolatedTests.length,
        byCategory: this.getTestsByCategory(),
        byStatus: this.getTestsByStatus()
      },
      isolatedTests: this.config.isolatedTests,
      thresholds: this.config.thresholds,
      recommendations: this.generateRecommendations()
    };

    const reportPath = path.join(this.reportsPath, `flake-isolation-report-${new Date().toISOString().split('T')[0]}.json`);
    fs.writeFileSync(reportPath, JSON.stringify(report, null, 2));
    
    // Also create a latest report
    const latestPath = path.join(this.reportsPath, 'latest-flake-isolation-report.json');
    fs.writeFileSync(latestPath, JSON.stringify(report, null, 2));
    
    console.log(`📊 Flake isolation report generated: ${reportPath}`);
    this.printSummary(report);
  }

  getTestsByCategory() {
    return this.config.isolatedTests.reduce((acc, test) => {
      acc[test.category] = (acc[test.category] || 0) + 1;
      return acc;
    }, {});
  }

  getTestsByStatus() {
    return this.config.isolatedTests.reduce((acc, test) => {
      acc[test.status] = (acc[test.status] || 0) + 1;
      return acc;
    }, {});
  }

  generateRecommendations() {
    const recommendations = [];
    
    const isolatedTests = this.config.isolatedTests.filter(t => t.status === 'isolated');
    const recoveredTests = this.config.isolatedTests.filter(t => t.status === 'recovered');
    
    if (isolatedTests.length > 5) {
      recommendations.push({
        priority: 'high',
        message: `High number of isolated tests (${isolatedTests.length}). Consider systematic test stability improvements.`
      });
    }
    
    if (recoveredTests.length > 0) {
      recommendations.push({
        priority: 'medium',
        message: `${recoveredTests.length} tests have recovered and may be ready for re-integration.`
      });
    }
    
    const oldIsolatedTests = isolatedTests.filter(test => {
      const daysSinceIsolation = (Date.now() - new Date(test.isolatedAt).getTime()) / (1000 * 60 * 60 * 24);
      return daysSinceIsolation > 7;
    });
    
    if (oldIsolatedTests.length > 0) {
      recommendations.push({
        priority: 'low',
        message: `${oldIsolatedTests.length} tests have been isolated for over a week. Consider recovery attempts.`
      });
    }
    
    return recommendations;
  }

  printSummary(report) {
    console.log('\n📋 FLAKE ISOLATION SUMMARY');
    console.log('=' .repeat(50));
    console.log(`Total isolated tests: ${report.summary.totalIsolated}`);
    console.log('\nBy category:');
    Object.entries(report.summary.byCategory).forEach(([category, count]) => {
      console.log(`  ${category}: ${count}`);
    });
    console.log('\nBy status:');
    Object.entries(report.summary.byStatus).forEach(([status, count]) => {
      console.log(`  ${status}: ${count}`);
    });
    
    if (report.recommendations.length > 0) {
      console.log('\n💡 RECOMMENDATIONS:');
      report.recommendations.forEach(rec => {
        console.log(`  [${rec.priority.toUpperCase()}] ${rec.message}`);
      });
    }
    console.log('=' .repeat(50));
  }

  async runDailyMaintenance() {
    console.log('🔧 Running daily flake isolation maintenance...');
    
    // Attempt recovery for tests isolated for more than 3 days
    const candidatesForRecovery = this.config.isolatedTests.filter(test => {
      if (test.status !== 'isolated') return false;
      
      const daysSinceIsolation = (Date.now() - new Date(test.isolatedAt).getTime()) / (1000 * 60 * 60 * 24);
      return daysSinceIsolation >= 3;
    });
    
    console.log(`🔄 Found ${candidatesForRecovery.length} tests eligible for recovery attempts`);
    
    for (const test of candidatesForRecovery) {
      console.log(`\n🎯 Attempting recovery for: ${test.pattern}`);
      await this.tryRecoverTest(test.pattern, 5); // Quick recovery test with 5 runs
    }
    
    this.generateFlakeReport();
    console.log('✅ Daily maintenance completed');
  }
}

// CLI interface
async function main() {
  const args = process.argv.slice(2);
  const command = args[0];
  const manager = new FlakeIsolationManager();

  switch (command) {
    case 'isolate':
      const pattern = args[1];
      const failureRate = args[2];
      if (!pattern) {
        console.error('Usage: flake-isolation-manager.js isolate <test-pattern> [failure-rate]');
        process.exit(1);
      }
      manager.isolateTest(pattern, { failureRate });
      break;

    case 'recover':
      const recoverPattern = args[1];
      const runs = parseInt(args[2]) || 10;
      if (!recoverPattern) {
        console.error('Usage: flake-isolation-manager.js recover <test-pattern> [runs]');
        process.exit(1);
      }
      await manager.tryRecoverTest(recoverPattern, runs);
      break;

    case 'remove':
      const removePattern = args[1];
      if (!removePattern) {
        console.error('Usage: flake-isolation-manager.js remove <test-pattern>');
        process.exit(1);
      }
      manager.removeTest(removePattern);
      break;

    case 'report':
      manager.generateFlakeReport();
      break;

    case 'maintenance':
      await manager.runDailyMaintenance();
      break;

    case 'list':
      console.log('📋 Currently isolated tests:');
      if (manager.config.isolatedTests.length === 0) {
        console.log('  (none)');
      } else {
        manager.config.isolatedTests.forEach((test, index) => {
          console.log(`  ${index + 1}. ${test.pattern} [${test.status}] - ${test.category}`);
          console.log(`     Isolated: ${test.isolatedAt}`);
          console.log(`     Failure rate: ${test.metadata.failureRate || 'unknown'}`);
        });
      }
      break;

    default:
      console.log('Flake Isolation Manager');
      console.log('Usage:');
      console.log('  isolate <test-pattern> [failure-rate]  - Isolate a flaky test');
      console.log('  recover <test-pattern> [runs]         - Attempt to recover a test');
      console.log('  remove <test-pattern>                 - Remove test from isolation');
      console.log('  report                                - Generate flake report');
      console.log('  maintenance                           - Run daily maintenance');
      console.log('  list                                  - List isolated tests');
      break;
  }
}

if (require.main === module) {
  main().catch(error => {
    console.error('❌ Error:', error.message);
    process.exit(1);
  });
}

module.exports = { FlakeIsolationManager };