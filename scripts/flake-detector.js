#!/usr/bin/env node

/**
 * Flake Detection Tool for ae-framework
 * Runs tests multiple times to detect flaky tests
 */

import { spawn } from 'child_process';
import fs from 'fs';
import path from 'path';

class FlakeDetector {
  constructor(options = {}) {
    this.runs = options.runs || 10;
    this.threshold = options.threshold || 0.1; // 10% failure rate considered flaky
    this.testPattern = options.testPattern || 'tests/**/*.test.ts';
    this.results = new Map();
    this.outputDir = options.outputDir || './flake-reports';
  }

  async runTests(run) {
    return new Promise((resolve, reject) => {
      console.log(`🔄 Running test suite (${run}/${this.runs})...`);
      
      const testProcess = spawn('npm', ['test'], {
        stdio: ['inherit', 'pipe', 'pipe']
      });

      let stdout = '';
      let stderr = '';

      testProcess.stdout.on('data', (data) => {
        stdout += data.toString();
      });

      testProcess.stderr.on('data', (data) => {
        stderr += data.toString();
      });

      testProcess.on('close', (code) => {
        resolve({
          run,
          success: code === 0,
          stdout,
          stderr,
          timestamp: new Date().toISOString()
        });
      });

      testProcess.on('error', (error) => {
        reject(error);
      });
    });
  }

  parseTestResults(output) {
    const tests = [];
    const lines = output.split('\n');
    
    for (const line of lines) {
      // Parse vitest output format
      if (line.includes('✓') || line.includes('✗') || line.includes('FAIL') || line.includes('PASS')) {
        const testMatch = line.match(/(\w+.*\.test\.ts)/);
        if (testMatch) {
          const testFile = testMatch[1];
          const passed = line.includes('✓') || line.includes('PASS');
          tests.push({
            file: testFile,
            name: testFile,
            passed
          });
        }
      }
    }
    
    return tests;
  }

  analyzeFlakiness() {
    const flakiness = new Map();
    
    for (const [testName, results] of this.results) {
      const totalRuns = results.length;
      const failures = results.filter(r => !r.passed).length;
      const failureRate = failures / totalRuns;
      
      if (failureRate > 0 && failureRate < 1) { // Not always passing or always failing
        flakiness.set(testName, {
          totalRuns,
          failures,
          successes: totalRuns - failures,
          failureRate,
          isFlaky: failureRate > this.threshold && failureRate < (1 - this.threshold)
        });
      }
    }
    
    return flakiness;
  }

  generateReport(flakiness) {
    if (!fs.existsSync(this.outputDir)) {
      fs.mkdirSync(this.outputDir, { recursive: true });
    }

    const reportPath = path.join(this.outputDir, `flake-report-${Date.now()}.json`);
    const summaryPath = path.join(this.outputDir, 'flake-summary.md');

    // Generate JSON report
    const report = {
      timestamp: new Date().toISOString(),
      configuration: {
        runs: this.runs,
        threshold: this.threshold,
        testPattern: this.testPattern
      },
      summary: {
        totalTests: this.results.size,
        flakyTests: Array.from(flakiness.values()).filter(f => f.isFlaky).length,
        overallFlakeRate: Array.from(flakiness.values()).length / this.results.size
      },
      flakyTests: Object.fromEntries(flakiness)
    };

    fs.writeFileSync(reportPath, JSON.stringify(report, null, 2));

    // Generate Markdown summary
    let markdown = `# Flake Detection Report\n\n`;
    markdown += `**Generated:** ${new Date().toISOString()}\n`;
    markdown += `**Runs:** ${this.runs}\n`;
    markdown += `**Threshold:** ${(this.threshold * 100).toFixed(1)}%\n\n`;

    const flakyTests = Array.from(flakiness.entries()).filter(([_, data]) => data.isFlaky);
    
    if (flakyTests.length === 0) {
      markdown += `## ✅ No Flaky Tests Detected\n\n`;
      markdown += `All ${this.results.size} tests showed consistent behavior across ${this.runs} runs.\n`;
    } else {
      markdown += `## 🚨 Flaky Tests Detected\n\n`;
      markdown += `Found ${flakyTests.length} flaky tests out of ${this.results.size} total tests.\n\n`;
      
      for (const [testName, data] of flakyTests) {
        markdown += `### ${testName}\n`;
        markdown += `- **Failure Rate:** ${(data.failureRate * 100).toFixed(1)}%\n`;
        markdown += `- **Successes:** ${data.successes}/${data.totalRuns}\n`;
        markdown += `- **Failures:** ${data.failures}/${data.totalRuns}\n\n`;
      }
    }

    fs.writeFileSync(summaryPath, markdown);

    console.log(`\n📊 Flake detection report generated:`);
    console.log(`   JSON: ${reportPath}`);
    console.log(`   Summary: ${summaryPath}`);

    return report;
  }

  async detectFlakes() {
    console.log(`🔍 Starting flake detection with ${this.runs} runs...`);
    
    const allRuns = [];
    
    // Run tests multiple times
    for (let i = 1; i <= this.runs; i++) {
      try {
        const result = await this.runTests(i);
        allRuns.push(result);
        
        // Parse individual test results
        const tests = this.parseTestResults(result.stdout + result.stderr);
        
        for (const test of tests) {
          if (!this.results.has(test.name)) {
            this.results.set(test.name, []);
          }
          this.results.get(test.name).push({
            run: i,
            passed: test.passed,
            timestamp: result.timestamp
          });
        }
        
        console.log(`   Run ${i}: ${result.success ? '✅ PASS' : '❌ FAIL'}`);
      } catch (error) {
        console.error(`   Run ${i}: ❌ ERROR - ${error.message}`);
      }
    }

    // Analyze results
    const flakiness = this.analyzeFlakiness();
    const report = this.generateReport(flakiness);

    // Print summary
    console.log(`\n📈 Flake Detection Summary:`);
    console.log(`   Total tests analyzed: ${this.results.size}`);
    console.log(`   Flaky tests found: ${Array.from(flakiness.values()).filter(f => f.isFlaky).length}`);
    console.log(`   Overall flake rate: ${(report.summary.overallFlakeRate * 100).toFixed(1)}%`);

    return report;
  }
}

// CLI interface
if (process.argv[1] === new URL(import.meta.url).pathname) {
  const args = process.argv.slice(2);
  const options = {};
  
  for (let i = 0; i < args.length; i += 2) {
    const key = args[i].replace('--', '');
    const value = args[i + 1];
    
    if (key === 'runs') options.runs = parseInt(value);
    if (key === 'threshold') options.threshold = parseFloat(value);
    if (key === 'pattern') options.testPattern = value;
    if (key === 'output') options.outputDir = value;
  }

  const detector = new FlakeDetector(options);
  detector.detectFlakes().catch(console.error);
}

export { FlakeDetector };