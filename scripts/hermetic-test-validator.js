#!/usr/bin/env node

/**
 * Hermetic Test Validator
 * Ensures tests are truly isolated and deterministic
 */

import fs from 'fs';
import path from 'path';
import { execSync } from 'child_process';

class HermeticTestValidator {
  constructor(options = {}) {
    this.testPattern = options.testPattern || 'tests/**/*.test.ts';
    this.runs = options.runs || 3;
    this.timeoutMs = options.timeoutMs || 30000;
    this.reportDir = options.reportDir || './hermetic-reports';
    
    this.violations = [];
    this.ensureDirectories();
  }

  ensureDirectories() {
    if (!fs.existsSync(this.reportDir)) {
      fs.mkdirSync(this.reportDir, { recursive: true });
    }
  }

  async validateHermeticProperties() {
    console.log('🔒 Validating hermetic test properties...\n');

    const results = {
      determinism: await this.testDeterminism(),
      isolation: await this.testIsolation(), 
      dependencies: await this.analyzeDependencies(),
      fileSystem: await this.analyzeFileSystemUsage(),
      network: await this.analyzeNetworkUsage(),
      timing: await this.analyzeTimingDependencies()
    };

    return results;
  }

  async testDeterminism() {
    console.log('🎲 Testing determinism (multiple runs)...');
    
    const results = [];
    
    for (let i = 1; i <= this.runs; i++) {
      console.log(`  Run ${i}/${this.runs}...`);
      
      try {
        const startTime = Date.now();
        const output = execSync('npm run test:fast', {
          encoding: 'utf-8',
          timeout: this.timeoutMs,
          stdio: ['pipe', 'pipe', 'pipe']
        });
        
        const duration = Date.now() - startTime;
        const testCount = this.extractTestCount(output);
        const passed = this.extractPassedCount(output);
        const failed = this.extractFailedCount(output);
        
        results.push({
          run: i,
          duration,
          testCount,
          passed,
          failed,
          success: failed === 0,
          output: output.slice(-500) // Last 500 chars for analysis
        });
        
      } catch (error) {
        results.push({
          run: i,
          error: error.message,
          success: false
        });
      }
    }

    // Analyze determinism
    const successful = results.filter(r => r.success);
    const deterministic = this.analyzeDeterminism(successful);
    
    return {
      runs: results.length,
      successful: successful.length,
      deterministic,
      results,
      score: this.calculateDeterminismScore(results)
    };
  }

  analyzeDeterminism(results) {
    if (results.length < 2) return false;
    
    const first = results[0];
    return results.every(result => 
      result.testCount === first.testCount &&
      result.passed === first.passed &&
      result.failed === first.failed
    );
  }

  calculateDeterminismScore(results) {
    const successRate = results.filter(r => r.success).length / results.length;
    const successful = results.filter(r => r.success);
    
    if (successful.length < 2) return 0;
    
    const deterministic = this.analyzeDeterminism(successful);
    return deterministic ? Math.round(successRate * 100) : 0;
  }

  async testIsolation() {
    console.log('🏝️  Testing isolation (parallel execution)...');
    
    try {
      // Test sequential execution
      console.log('  Sequential execution...');
      const sequentialStart = Date.now();
      execSync('npm run test:fast', { encoding: 'utf-8', timeout: this.timeoutMs });
      const sequentialDuration = Date.now() - sequentialStart;
      
      // Test parallel execution (if supported)
      console.log('  Parallel execution...');
      const parallelStart = Date.now();
      execSync('npm run test:fast -- --reporter=basic', { 
        encoding: 'utf-8', 
        timeout: this.timeoutMs,
        env: { ...process.env, VITEST_POOL_OPTIONS: '{"threads":{"maxThreads":4}}' }
      });
      const parallelDuration = Date.now() - parallelStart;
      
      const speedup = sequentialDuration / parallelDuration;
      const isolated = speedup > 0.5; // If parallel is significantly faster, tests are likely isolated
      
      return {
        sequential: sequentialDuration,
        parallel: parallelDuration,
        speedup: Math.round(speedup * 100) / 100,
        isolated,
        score: isolated ? 80 : 40
      };
      
    } catch (error) {
      return {
        error: error.message,
        isolated: false,
        score: 0
      };
    }
  }

  async analyzeDependencies() {
    console.log('📦 Analyzing external dependencies...');
    
    const testFiles = this.findTestFiles();
    const issues = [];
    
    for (const file of testFiles) {
      const content = fs.readFileSync(file, 'utf-8');
      
      // Check for external dependencies
      const externalDeps = this.findExternalDependencies(content, file);
      issues.push(...externalDeps);
    }
    
    const score = Math.max(0, 100 - (issues.length * 10));
    
    return {
      filesAnalyzed: testFiles.length,
      issues,
      score
    };
  }

  findExternalDependencies(content, filepath) {
    const issues = [];
    const lines = content.split('\n');
    
    lines.forEach((line, index) => {
      // Check for network calls
      if (line.includes('fetch(') || line.includes('axios.') || line.includes('http.')) {
        issues.push({
          type: 'network',
          file: filepath,
          line: index + 1,
          code: line.trim(),
          message: 'Test contains network calls - should be mocked'
        });
      }
      
      // Check for file system operations
      if (line.includes('fs.') && !line.includes('mock') && !line.includes('stub')) {
        issues.push({
          type: 'filesystem',
          file: filepath,
          line: index + 1,
          code: line.trim(),
          message: 'Test contains file system operations - should be isolated'
        });
      }
      
      // Check for database connections
      if (line.includes('connect(') || line.includes('db.') || line.includes('pool.')) {
        issues.push({
          type: 'database',
          file: filepath,
          line: index + 1,
          code: line.trim(),
          message: 'Test contains database operations - should be mocked'
        });
      }
      
      // Check for process/environment dependencies
      if (line.includes('process.env') && !line.includes('NODE_ENV')) {
        issues.push({
          type: 'environment',
          file: filepath,
          line: index + 1,
          code: line.trim(),
          message: 'Test depends on environment variables - should be controlled'
        });
      }
    });
    
    return issues;
  }

  async analyzeFileSystemUsage() {
    console.log('📁 Analyzing file system usage...');
    
    const testFiles = this.findTestFiles();
    const fsUsage = [];
    
    for (const file of testFiles) {
      const content = fs.readFileSync(file, 'utf-8');
      
      // Look for file operations
      const fsOps = content.match(/fs\.\w+|readFile|writeFile|mkdir|rmdir/g) || [];
      const tempFiles = content.match(/\/tmp\/|temp|\.tmp/g) || [];
      
      if (fsOps.length > 0 || tempFiles.length > 0) {
        fsUsage.push({
          file,
          fsOperations: fsOps.length,
          tempFiles: tempFiles.length,
          isolated: content.includes('mock') || content.includes('stub') || tempFiles.length > 0
        });
      }
    }
    
    const isolatedCount = fsUsage.filter(f => f.isolated).length;
    const score = fsUsage.length === 0 ? 100 : Math.round((isolatedCount / fsUsage.length) * 100);
    
    return {
      filesWithFsUsage: fsUsage.length,
      isolatedFiles: isolatedCount,
      usage: fsUsage,
      score
    };
  }

  async analyzeNetworkUsage() {
    console.log('🌐 Analyzing network usage...');
    
    const testFiles = this.findTestFiles();
    const networkUsage = [];
    
    for (const file of testFiles) {
      const content = fs.readFileSync(file, 'utf-8');
      
      // Look for network operations
      const networkOps = content.match(/fetch\(|axios\.|http\.|request\(/g) || [];
      const mocked = content.includes('mock') || content.includes('nock') || content.includes('msw');
      
      if (networkOps.length > 0) {
        networkUsage.push({
          file,
          networkOperations: networkOps.length,
          mocked
        });
      }
    }
    
    const mockedCount = networkUsage.filter(f => f.mocked).length;
    const score = networkUsage.length === 0 ? 100 : Math.round((mockedCount / networkUsage.length) * 100);
    
    return {
      filesWithNetworkUsage: networkUsage.length,
      mockedFiles: mockedCount,
      usage: networkUsage,
      score
    };
  }

  async analyzeTimingDependencies() {
    console.log('⏰ Analyzing timing dependencies...');
    
    const testFiles = this.findTestFiles();
    const timingIssues = [];
    
    for (const file of testFiles) {
      const content = fs.readFileSync(file, 'utf-8');
      
      // Look for timing-dependent code
      const sleeps = content.match(/sleep\(|setTimeout\(|setInterval\(/g) || [];
      const dates = content.match(/new Date\(\)|Date\.now\(\)/g) || [];
      const waits = content.match(/waitFor|wait\(/g) || [];
      
      if (sleeps.length > 0 || dates.length > 0 || waits.length > 0) {
        timingIssues.push({
          file,
          sleeps: sleeps.length,
          dates: dates.length,
          waits: waits.length,
          hasMocks: content.includes('jest.useFakeTimers') || content.includes('vi.useFakeTimers')
        });
      }
    }
    
    const withMocks = timingIssues.filter(f => f.hasMocks).length;
    const score = timingIssues.length === 0 ? 100 : Math.round((withMocks / timingIssues.length) * 100);
    
    return {
      filesWithTimingDeps: timingIssues.length,
      filesWithMockedTiming: withMocks,
      issues: timingIssues,
      score
    };
  }

  findTestFiles() {
    const testFiles = [];
    
    const scanDir = (dir) => {
      if (!fs.existsSync(dir)) return;
      
      const entries = fs.readdirSync(dir, { withFileTypes: true });
      
      for (const entry of entries) {
        const fullPath = path.join(dir, entry.name);
        
        if (entry.isDirectory() && !entry.name.startsWith('.') && entry.name !== 'node_modules') {
          scanDir(fullPath);
        } else if (entry.isFile() && (entry.name.endsWith('.test.ts') || entry.name.endsWith('.spec.ts'))) {
          testFiles.push(fullPath);
        }
      }
    };
    
    scanDir('./tests');
    scanDir('./src');
    
    return testFiles;
  }

  extractTestCount(output) {
    const match = output.match(/(\d+) passed/);
    return match ? parseInt(match[1]) : 0;
  }

  extractPassedCount(output) {
    const match = output.match(/(\d+) passed/);
    return match ? parseInt(match[1]) : 0;
  }

  extractFailedCount(output) {
    const match = output.match(/(\d+) failed/);
    return match ? parseInt(match[1]) : 0;
  }

  calculateOverallScore(results) {
    const weights = {
      determinism: 0.3,
      isolation: 0.2,
      dependencies: 0.2,
      fileSystem: 0.1,
      network: 0.1,
      timing: 0.1
    };
    
    let weightedScore = 0;
    
    for (const [category, result] of Object.entries(results)) {
      if (weights[category] && result.score !== undefined) {
        weightedScore += result.score * weights[category];
      }
    }
    
    return Math.round(weightedScore);
  }

  generateReport(results) {
    const overallScore = this.calculateOverallScore(results);
    
    let report = '# Hermetic Test Validation Report\n\n';
    report += `**Generated:** ${new Date().toISOString()}\n`;
    report += `**Overall Score:** ${this.getScoreEmoji(overallScore)} ${overallScore}/100\n`;
    report += `**Hermetic Level:** ${this.getHermeticLevel(overallScore)}\n\n`;

    // Summary table
    report += '## 📊 Hermetic Properties Summary\n\n';
    report += '| Property | Score | Status | Issues |\n';
    report += '|----------|-------|--------|---------|\n';
    
    Object.entries(results).forEach(([category, result]) => {
      const score = result.score || 0;
      const emoji = this.getScoreEmoji(score);
      const issues = result.issues?.length || result.usage?.length || 0;
      
      report += `| ${category.charAt(0).toUpperCase() + category.slice(1)} | ${score}/100 | ${emoji} | ${issues} |\n`;
    });
    report += '\n';

    // Detailed results
    Object.entries(results).forEach(([category, result]) => {
      report += `## ${category.charAt(0).toUpperCase() + category.slice(1)} Analysis\n\n`;
      
      if (result.score !== undefined) {
        report += `**Score:** ${result.score}/100\n\n`;
      }
      
      if (result.issues && result.issues.length > 0) {
        report += '### Issues Found\n\n';
        result.issues.forEach(issue => {
          report += `- **${issue.type}** in \`${issue.file}\`:${issue.line}\n`;
          report += `  ${issue.message}\n`;
          report += `  \`${issue.code}\`\n\n`;
        });
      }
      
      if (result.usage && result.usage.length > 0) {
        report += '### Files with Issues\n\n';
        result.usage.forEach(usage => {
          report += `- \`${usage.file}\`\n`;
          Object.entries(usage).forEach(([key, value]) => {
            if (key !== 'file' && typeof value === 'number' && value > 0) {
              report += `  - ${key}: ${value}\n`;
            }
          });
          report += '\n';
        });
      }
    });

    // Recommendations
    report += '## 📋 Recommendations\n\n';
    
    if (overallScore < 50) {
      report += '🚨 **Critical hermetic violations detected!**\n\n';
      report += '1. Implement proper test isolation immediately\n';
      report += '2. Mock all external dependencies\n';
      report += '3. Use fake timers for time-dependent tests\n';
      report += '4. Avoid file system operations in tests\n\n';
    } else if (overallScore < 80) {
      report += '⚠️ **Hermetic improvements needed**\n\n';
      report += '1. Address remaining external dependencies\n';
      report += '2. Improve test determinism\n';
      report += '3. Consider using test containers for integration tests\n';
      report += '4. Review and mock timing dependencies\n\n';
    } else {
      report += '✅ **Good hermetic test practices**\n\n';
      report += '1. Continue monitoring hermetic properties\n';
      report += '2. Add hermetic validation to CI pipeline\n';
      report += '3. Document best practices for new tests\n\n';
    }

    return report;
  }

  getScoreEmoji(score) {
    if (score >= 90) return '🌟';
    if (score >= 80) return '✅';
    if (score >= 70) return '🟢';
    if (score >= 60) return '🟡';
    if (score >= 40) return '🟠';
    return '🔴';
  }

  getHermeticLevel(score) {
    if (score >= 90) return 'EXCELLENT';
    if (score >= 80) return 'GOOD';
    if (score >= 60) return 'FAIR';
    if (score >= 40) return 'POOR';
    return 'CRITICAL';
  }

  async runCompleteValidation() {
    console.log('🔒 Running complete hermetic test validation...\n');

    const results = await this.validateHermeticProperties();
    const overallScore = this.calculateOverallScore(results);
    
    const report = this.generateReport(results);
    
    // Save report
    const timestamp = new Date().toISOString().replace(/[:.]/g, '-');
    const reportPath = path.join(this.reportDir, `hermetic-validation-${timestamp}.md`);
    fs.writeFileSync(reportPath, report);
    
    // Also save as latest
    fs.writeFileSync(path.join(this.reportDir, 'latest-hermetic-report.md'), report);
    
    console.log('\n🔒 Hermetic Test Validation Complete!\n');
    console.log(`Overall Score: ${overallScore}/100 (${this.getHermeticLevel(overallScore)})`);
    console.log(`Report saved: ${reportPath}\n`);

    return {
      overallScore,
      results,
      reportPath,
      level: this.getHermeticLevel(overallScore)
    };
  }
}

// CLI interface
if (process.argv[1] === new URL(import.meta.url).pathname) {
  const validator = new HermeticTestValidator();
  validator.runCompleteValidation().catch(console.error);
}

export { HermeticTestValidator };