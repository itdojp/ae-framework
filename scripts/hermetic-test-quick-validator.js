#!/usr/bin/env node

/**
 * Quick Hermetic Test Validator
 * Static analysis of hermetic test properties
 */

import fs from 'fs';
import path from 'path';

class QuickHermeticValidator {
  constructor(options = {}) {
    this.reportDir = options.reportDir || './hermetic-reports';
    this.ensureDirectories();
  }

  ensureDirectories() {
    if (!fs.existsSync(this.reportDir)) {
      fs.mkdirSync(this.reportDir, { recursive: true });
    }
  }

  async validateHermeticProperties() {
    console.log('🔒 Quick hermetic test validation...\n');

    const results = {
      dependencies: await this.analyzeDependencies(),
      fileSystem: await this.analyzeFileSystemUsage(),
      network: await this.analyzeNetworkUsage(),
      timing: await this.analyzeTimingDependencies(),
      testStructure: await this.analyzeTestStructure()
    };

    return results;
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

  async analyzeTestStructure() {
    console.log('🏗️  Analyzing test structure...');
    
    const testFiles = this.findTestFiles();
    let totalTests = 0;
    let isolatedTests = 0;
    
    for (const file of testFiles) {
      const content = fs.readFileSync(file, 'utf-8');
      
      // Count test cases
      const testCases = content.match(/it\(|test\(|describe\(/g) || [];
      totalTests += testCases.length;
      
      // Check for proper test isolation patterns
      const hasBeforeEach = content.includes('beforeEach');
      const hasAfterEach = content.includes('afterEach');
      const hasMockReset = content.includes('clearAllMocks') || content.includes('resetAllMocks');
      
      if (hasBeforeEach || hasAfterEach || hasMockReset) {
        isolatedTests += testCases.length;
      }
    }
    
    const score = totalTests === 0 ? 100 : Math.round((isolatedTests / totalTests) * 100);
    
    return {
      totalTestFiles: testFiles.length,
      totalTests,
      isolatedTests,
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

  calculateOverallScore(results) {
    const weights = {
      dependencies: 0.3,
      fileSystem: 0.2,
      network: 0.2,
      timing: 0.2,
      testStructure: 0.1
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
    
    let report = '# Quick Hermetic Test Validation Report\n\n';
    report += `**Generated:** ${new Date().toISOString()}\n`;
    report += `**Overall Score:** ${this.getScoreEmoji(overallScore)} ${overallScore}/100\n`;
    report += `**Hermetic Level:** ${this.getHermeticLevel(overallScore)}\n\n`;

    // Summary table
    report += '## 📊 Hermetic Properties Summary\n\n';
    report += '| Property | Score | Status | Issues |\n';
    report += '|----------|-------|--------|--------|\n';
    
    Object.entries(results).forEach(([category, result]) => {
      const score = result.score || 0;
      const emoji = this.getScoreEmoji(score);
      const issues = result.issues?.length || result.usage?.length || 0;
      
      report += `| ${category.charAt(0).toUpperCase() + category.slice(1)} | ${score}/100 | ${emoji} | ${issues} |\n`;
    });
    report += '\n';

    // Critical findings
    const criticalIssues = [];
    Object.entries(results).forEach(([category, result]) => {
      if (result.issues && result.issues.length > 0) {
        criticalIssues.push(...result.issues.map(issue => ({...issue, category})));
      }
    });

    if (criticalIssues.length > 0) {
      report += '## 🚨 Critical Hermetic Violations\n\n';
      criticalIssues.slice(0, 10).forEach(issue => {
        report += `- **${issue.type}** in \`${issue.file}\`:${issue.line}\n`;
        report += `  ${issue.message}\n`;
        report += `  \`${issue.code}\`\n\n`;
      });
      
      if (criticalIssues.length > 10) {
        report += `... and ${criticalIssues.length - 10} more issues\n\n`;
      }
    }

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
      report += '2. Add proper test setup/teardown\n';
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

  async runQuickValidation() {
    console.log('🔒 Running quick hermetic test validation...\n');

    const results = await this.validateHermeticProperties();
    const overallScore = this.calculateOverallScore(results);
    
    const report = this.generateReport(results);
    
    // Save report
    const timestamp = new Date().toISOString().replace(/[:.]/g, '-');
    const reportPath = path.join(this.reportDir, `quick-hermetic-validation-${timestamp}.md`);
    fs.writeFileSync(reportPath, report);
    
    // Also save as latest
    fs.writeFileSync(path.join(this.reportDir, 'latest-quick-hermetic-report.md'), report);
    
    console.log('\n🔒 Quick Hermetic Test Validation Complete!\n');
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
  const validator = new QuickHermeticValidator();
  validator.runQuickValidation().catch(console.error);
}

export { QuickHermeticValidator };