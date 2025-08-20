#!/usr/bin/env node

/**
 * Benchmark Regression Detection System
 * Detects performance regressions by comparing benchmark results
 */

import fs from 'fs';
import path from 'path';
import { execSync } from 'child_process';

class BenchmarkRegressionDetector {
  constructor(options = {}) {
    this.baselineDir = options.baselineDir || './benchmarks/baseline';
    this.currentDir = options.currentDir || './benchmarks/current';
    this.reportDir = options.reportDir || './benchmarks/reports';
    this.thresholds = {
      performance: options.performanceThreshold || 0.1, // 10% regression threshold
      memory: options.memoryThreshold || 0.15, // 15% memory increase threshold
      critical: options.criticalThreshold || 0.25 // 25% critical threshold
    };
    
    this.ensureDirectories();
  }

  ensureDirectories() {
    [this.baselineDir, this.currentDir, this.reportDir].forEach(dir => {
      if (!fs.existsSync(dir)) {
        fs.mkdirSync(dir, { recursive: true });
      }
    });
  }

  async runBenchmarkSuite() {
    console.log('🏃 Running benchmark suite...');
    
    const benchmarks = [
      {
        name: 'static-analysis-performance',
        description: 'TypeScript compilation and linting performance',
        command: 'npm run test:types',
        category: 'build'
      },
      {
        name: 'test-execution-performance', 
        description: 'Test suite execution performance',
        command: 'npm run test:fast',
        category: 'testing'
      },
      {
        name: 'ir-validation-performance',
        description: 'IR schema validation performance',
        command: 'npm run ir:validate:project',
        category: 'validation'
      },
      {
        name: 'package-analysis-performance',
        description: 'Package quality analysis performance', 
        command: 'npm run package:quality',
        category: 'analysis'
      }
    ];

    const results = [];
    
    for (const benchmark of benchmarks) {
      console.log(`  📊 Running ${benchmark.name}...`);
      
      const result = await this.runSingleBenchmark(benchmark);
      results.push(result);
      
      console.log(`    ⏱️  Duration: ${result.duration}ms`);
      console.log(`    💾 Memory: ${result.memory.peak}MB peak`);
    }

    return results;
  }

  async runSingleBenchmark(benchmark) {
    const startTime = Date.now();
    const startMemory = process.memoryUsage();
    
    let success = false;
    let error = null;
    let output = '';
    
    try {
      // Run the benchmark command with timeout
      output = execSync(benchmark.command, { 
        encoding: 'utf-8',
        timeout: 300000, // 5 minute timeout
        stdio: ['pipe', 'pipe', 'pipe']
      });
      success = true;
    } catch (err) {
      error = err.message;
      output = err.stdout || err.stderr || '';
    }
    
    const endTime = Date.now();
    const endMemory = process.memoryUsage();
    
    return {
      name: benchmark.name,
      description: benchmark.description,
      category: benchmark.category,
      success,
      error,
      duration: endTime - startTime,
      memory: {
        start: Math.round(startMemory.heapUsed / 1024 / 1024),
        end: Math.round(endMemory.heapUsed / 1024 / 1024),
        peak: Math.round(Math.max(startMemory.heapUsed, endMemory.heapUsed) / 1024 / 1024),
        delta: Math.round((endMemory.heapUsed - startMemory.heapUsed) / 1024 / 1024)
      },
      timestamp: new Date().toISOString(),
      output: output.slice(0, 1000) // Truncate long output
    };
  }

  async saveCurrentResults(results) {
    const timestamp = new Date().toISOString().replace(/[:.]/g, '-');
    const filename = `benchmark-${timestamp}.json`;
    const filepath = path.join(this.currentDir, filename);
    
    const data = {
      timestamp: new Date().toISOString(),
      results,
      metadata: {
        nodeVersion: process.version,
        platform: process.platform,
        arch: process.arch,
        cpus: (await import('os')).cpus().length
      }
    };
    
    fs.writeFileSync(filepath, JSON.stringify(data, null, 2));
    
    // Also save as 'latest.json' for easy access
    fs.writeFileSync(path.join(this.currentDir, 'latest.json'), JSON.stringify(data, null, 2));
    
    console.log(`💾 Benchmark results saved: ${filepath}`);
    return filepath;
  }

  loadBaseline() {
    const baselinePath = path.join(this.baselineDir, 'baseline.json');
    
    if (!fs.existsSync(baselinePath)) {
      console.log('📈 No baseline found, creating from current results...');
      return null;
    }
    
    try {
      const baseline = JSON.parse(fs.readFileSync(baselinePath, 'utf-8'));
      console.log(`📊 Loaded baseline from ${baseline.timestamp}`);
      return baseline;
    } catch (error) {
      console.warn(`⚠️ Failed to load baseline: ${error.message}`);
      return null;
    }
  }

  async setBaseline(results) {
    const baselinePath = path.join(this.baselineDir, 'baseline.json');
    
    const baseline = {
      timestamp: new Date().toISOString(),
      results,
      metadata: {
        nodeVersion: process.version,
        platform: process.platform,
        arch: process.arch,
        cpus: (await import('os')).cpus().length
      }
    };
    
    fs.writeFileSync(baselinePath, JSON.stringify(baseline, null, 2));
    console.log(`📊 New baseline established: ${baselinePath}`);
  }

  detectRegressions(current, baseline) {
    if (!baseline) {
      return { regressions: [], summary: { total: 0, critical: 0, warning: 0 } };
    }

    const regressions = [];
    
    for (const currentResult of current) {
      const baselineResult = baseline.results.find(r => r.name === currentResult.name);
      
      if (!baselineResult) {
        continue; // New benchmark, no regression to detect
      }
      
      // Check performance regression
      const durationRegression = (currentResult.duration - baselineResult.duration) / baselineResult.duration;
      const memoryRegression = (currentResult.memory.peak - baselineResult.memory.peak) / baselineResult.memory.peak;
      
      const regression = {
        benchmark: currentResult.name,
        category: currentResult.category,
        regressions: []
      };
      
      if (durationRegression > this.thresholds.performance) {
        const severity = durationRegression > this.thresholds.critical ? 'critical' : 'warning';
        regression.regressions.push({
          type: 'performance',
          severity,
          current: currentResult.duration,
          baseline: baselineResult.duration,
          change: durationRegression,
          changePercent: Math.round(durationRegression * 100),
          message: `Performance regression: ${Math.round(durationRegression * 100)}% slower`
        });
      }
      
      if (memoryRegression > this.thresholds.memory) {
        const severity = memoryRegression > this.thresholds.critical ? 'critical' : 'warning';
        regression.regressions.push({
          type: 'memory',
          severity,
          current: currentResult.memory.peak,
          baseline: baselineResult.memory.peak,
          change: memoryRegression,
          changePercent: Math.round(memoryRegression * 100),
          message: `Memory regression: ${Math.round(memoryRegression * 100)}% increase`
        });
      }
      
      if (regression.regressions.length > 0) {
        regressions.push(regression);
      }
    }
    
    const summary = {
      total: regressions.reduce((sum, r) => sum + r.regressions.length, 0),
      critical: regressions.reduce((sum, r) => sum + r.regressions.filter(reg => reg.severity === 'critical').length, 0),
      warning: regressions.reduce((sum, r) => sum + r.regressions.filter(reg => reg.severity === 'warning').length, 0)
    };
    
    return { regressions, summary };
  }

  generateRegressionReport(current, baseline, regressions) {
    const timestamp = new Date().toISOString();
    
    let report = '# Benchmark Regression Analysis Report\n\n';
    report += `**Generated:** ${timestamp}\n`;
    report += `**Status:** ${regressions.summary.total === 0 ? '✅ No regressions detected' : '⚠️ Regressions detected'}\n\n`;

    // Summary
    report += '## 📊 Summary\n\n';
    if (baseline) {
      report += `**Baseline:** ${baseline.timestamp}\n`;
      report += `**Current:** ${current[0]?.timestamp || timestamp}\n`;
    } else {
      report += `**Baseline:** No baseline available\n`;
    }
    report += `**Total Regressions:** ${regressions.summary.total}\n`;
    report += `**Critical:** ${regressions.summary.critical}\n`;
    report += `**Warnings:** ${regressions.summary.warning}\n\n`;

    // Performance comparison table
    report += '## 📈 Performance Comparison\n\n';
    report += '| Benchmark | Current | Baseline | Change | Status |\n';
    report += '|-----------|---------|----------|--------|---------|\n';
    
    for (const result of current) {
      const baselineResult = baseline?.results.find(r => r.name === result.name);
      const regression = regressions.regressions.find(r => r.benchmark === result.name);
      
      if (baselineResult) {
        const durationChange = ((result.duration - baselineResult.duration) / baselineResult.duration * 100).toFixed(1);
        const status = regression ? (regression.regressions.some(r => r.severity === 'critical') ? '🚨' : '⚠️') : '✅';
        
        report += `| ${result.name} | ${result.duration}ms | ${baselineResult.duration}ms | ${durationChange}% | ${status} |\n`;
      } else {
        report += `| ${result.name} | ${result.duration}ms | N/A | New | 🆕 |\n`;
      }
    }
    report += '\n';

    // Regression details
    if (regressions.regressions.length > 0) {
      report += '## 🚨 Detected Regressions\n\n';
      
      for (const regression of regressions.regressions) {
        report += `### ${regression.benchmark}\n\n`;
        
        for (const reg of regression.regressions) {
          const emoji = reg.severity === 'critical' ? '🚨' : '⚠️';
          report += `${emoji} **${reg.type.toUpperCase()} REGRESSION**\n`;
          report += `- ${reg.message}\n`;
          report += `- Current: ${reg.current}${reg.type === 'performance' ? 'ms' : 'MB'}\n`;
          report += `- Baseline: ${reg.baseline}${reg.type === 'performance' ? 'ms' : 'MB'}\n\n`;
        }
      }
    }

    // Recommendations
    report += '## 📋 Recommendations\n\n';
    
    if (regressions.summary.critical > 0) {
      report += '🚨 **Critical regressions detected!**\n';
      report += '1. Investigate and fix critical performance regressions immediately\n';
      report += '2. Consider reverting recent changes if regression source is unclear\n';
      report += '3. Run focused benchmarks to isolate the issue\n\n';
    } else if (regressions.summary.warning > 0) {
      report += '⚠️ **Performance warnings detected**\n';
      report += '1. Monitor these regressions in subsequent runs\n';
      report += '2. Consider optimizing the affected components\n';
      report += '3. Update baseline if performance changes are intentional\n\n';
    } else {
      report += '✅ **No performance regressions detected**\n';
      report += '1. Continue monitoring performance in future runs\n';
      report += '2. Consider updating baseline periodically\n';
      report += '3. Add more comprehensive benchmarks as needed\n\n';
    }

    return report;
  }

  saveReport(report) {
    const timestamp = new Date().toISOString().replace(/[:.]/g, '-');
    const filename = `regression-report-${timestamp}.md`;
    const filepath = path.join(this.reportDir, filename);
    
    fs.writeFileSync(filepath, report);
    
    // Also save as latest report
    fs.writeFileSync(path.join(this.reportDir, 'latest-regression-report.md'), report);
    
    console.log(`📄 Regression report saved: ${filepath}`);
    return filepath;
  }

  async runCompleteAnalysis() {
    console.log('🏁 Running complete benchmark regression analysis...\n');

    // Run current benchmarks
    const currentResults = await this.runBenchmarkSuite();
    
    // Save current results
    await this.saveCurrentResults(currentResults);
    
    // Load baseline for comparison
    const baseline = this.loadBaseline();
    
    // Detect regressions
    const regressions = this.detectRegressions(currentResults, baseline);
    
    // Generate report
    const report = this.generateRegressionReport(currentResults, baseline, regressions);
    const reportPath = this.saveReport(report);
    
    // Summary
    console.log('\n🏁 Benchmark Regression Analysis Complete!\n');
    console.log(`Benchmarks Run: ${currentResults.length}`);
    console.log(`Total Regressions: ${regressions.summary.total}`);
    console.log(`Critical: ${regressions.summary.critical}`);
    console.log(`Warnings: ${regressions.summary.warning}`);
    console.log(`Report: ${reportPath}\n`);

    return {
      currentResults,
      baseline,
      regressions,
      reportPath,
      status: regressions.summary.critical > 0 ? 'critical' : 
              regressions.summary.warning > 0 ? 'warning' : 'passed'
    };
  }
}

// CLI interface
if (process.argv[1] === new URL(import.meta.url).pathname) {
  const args = process.argv.slice(2);
  
  if (args.includes('--help') || args.includes('-h')) {
    console.log(`
Benchmark Regression Detection System

Usage:
  node benchmark-regression-detector.js [options]

Options:
  --set-baseline    Set current results as new baseline
  --help, -h        Show this help

Examples:
  node benchmark-regression-detector.js
  node benchmark-regression-detector.js --set-baseline
`);
    process.exit(0);
  }

  const detector = new BenchmarkRegressionDetector();
  
  if (args.includes('--set-baseline')) {
    detector.runBenchmarkSuite().then(async results => {
      await detector.setBaseline(results);
      console.log('✅ Baseline updated successfully');
    }).catch(console.error);
  } else {
    detector.runCompleteAnalysis().then(result => {
      process.exit(result.status === 'critical' ? 1 : 0);
    }).catch(console.error);
  }
}

export { BenchmarkRegressionDetector };