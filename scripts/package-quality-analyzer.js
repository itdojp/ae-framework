#!/usr/bin/env node

/**
 * Package Quality Analyzer for ae-framework
 * Comprehensive analysis of package.json quality and dependencies
 */

import fs from 'fs';
import path from 'path';
import { execSync } from 'child_process';

class PackageQualityAnalyzer {
  constructor(packagePath = './package.json') {
    this.packagePath = packagePath;
    this.packageData = this.loadPackageJson();
    this.analysisRules = this.initializeRules();
  }

  loadPackageJson() {
    try {
      const content = fs.readFileSync(this.packagePath, 'utf-8');
      return JSON.parse(content);
    } catch (error) {
      throw new Error(`Failed to load package.json: ${error.message}`);
    }
  }

  initializeRules() {
    return [
      {
        id: 'PKG_001',
        name: 'Required Fields',
        description: 'Package must have essential fields',
        severity: 'error',
        check: (pkg) => {
          const required = ['name', 'version', 'description'];
          const missing = required.filter(field => !pkg[field]);
          return {
            passed: missing.length === 0,
            details: missing.length > 0 ? `Missing: ${missing.join(', ')}` : 'All required fields present'
          };
        }
      },
      {
        id: 'PKG_002',
        name: 'Version Format',
        description: 'Version must follow semantic versioning',
        severity: 'error',
        check: (pkg) => {
          const semverRegex = /^\d+\.\d+\.\d+(-[a-zA-Z0-9\-.]+)?(\+[a-zA-Z0-9\-.]+)?$/;
          const valid = semverRegex.test(pkg.version);
          return {
            passed: valid,
            details: valid ? 'Valid semver format' : `Invalid version: ${pkg.version}`
          };
        }
      },
      {
        id: 'PKG_003',
        name: 'Script Quality',
        description: 'Essential scripts should be present',
        severity: 'warning',
        check: (pkg) => {
          const essential = ['test', 'build', 'lint'];
          const present = essential.filter(script => pkg.scripts && pkg.scripts[script]);
          const coverage = (present.length / essential.length) * 100;
          return {
            passed: coverage >= 66,
            details: `${present.length}/${essential.length} essential scripts (${coverage.toFixed(0)}%)`
          };
        }
      },
      {
        id: 'PKG_004',
        name: 'Dependency Count',
        description: 'Reasonable number of dependencies',
        severity: 'warning',
        check: (pkg) => {
          const depCount = Object.keys(pkg.dependencies || {}).length;
          const devDepCount = Object.keys(pkg.devDependencies || {}).length;
          const total = depCount + devDepCount;
          const reasonable = total <= 150; // Reasonable for a large framework
          return {
            passed: reasonable,
            details: `${total} total deps (${depCount} prod, ${devDepCount} dev)`
          };
        }
      },
      {
        id: 'PKG_005',
        name: 'License Present',
        description: 'Package should have a license',
        severity: 'warning',
        check: (pkg) => {
          const hasLicense = pkg.license || pkg.licenses;
          return {
            passed: !!hasLicense,
            details: hasLicense ? `License: ${pkg.license}` : 'No license specified'
          };
        }
      },
      {
        id: 'PKG_006',
        name: 'Repository Info',
        description: 'Repository information should be present',
        severity: 'info',
        check: (pkg) => {
          const hasRepo = pkg.repository;
          return {
            passed: !!hasRepo,
            details: hasRepo ? 'Repository info present' : 'No repository info'
          };
        }
      },
      {
        id: 'PKG_007',
        name: 'Keywords Present',
        description: 'Keywords help with discoverability',
        severity: 'info',
        check: (pkg) => {
          const hasKeywords = pkg.keywords && pkg.keywords.length > 0;
          return {
            passed: hasKeywords,
            details: hasKeywords ? `${pkg.keywords.length} keywords` : 'No keywords'
          };
        }
      },
      {
        id: 'PKG_008',
        name: 'Engine Constraints',
        description: 'Engine constraints help ensure compatibility',
        severity: 'info',
        check: (pkg) => {
          const hasEngines = pkg.engines && Object.keys(pkg.engines).length > 0;
          return {
            passed: hasEngines,
            details: hasEngines ? `Engines: ${Object.keys(pkg.engines).join(', ')}` : 'No engine constraints'
          };
        }
      },
      {
        id: 'PKG_009',
        name: 'Script Naming',
        description: 'Scripts should follow naming conventions',
        severity: 'warning',
        check: (pkg) => {
          if (!pkg.scripts) return { passed: true, details: 'No scripts to check' };
          
          const problematic = [];
          const scriptNames = Object.keys(pkg.scripts);
          
          // Check for common bad patterns
          scriptNames.forEach(name => {
            if (name.includes(' ')) problematic.push(`"${name}" contains spaces`);
            if (name.length > 50) problematic.push(`"${name}" is too long`);
            if (!/^[a-z0-9\-:]+$/.test(name)) problematic.push(`"${name}" uses invalid characters`);
          });
          
          return {
            passed: problematic.length === 0,
            details: problematic.length > 0 ? problematic.join('; ') : 'All script names valid'
          };
        }
      },
      {
        id: 'PKG_010',
        name: 'Security Scripts',
        description: 'Security-related scripts should be present',
        severity: 'info',
        check: (pkg) => {
          const securityScripts = ['audit', 'security:scan', 'verify:security'];
          const present = securityScripts.filter(script => 
            pkg.scripts && Object.keys(pkg.scripts).some(s => s.includes(script.split(':')[0]))
          );
          return {
            passed: present.length > 0,
            details: present.length > 0 ? `Security scripts: ${present.length}` : 'No security scripts found'
          };
        }
      }
    ];
  }

  async analyzePackage() {
    console.log('📦 Analyzing package quality...\n');
    
    const results = {
      overall: 'unknown',
      score: 0,
      totalChecks: this.analysisRules.length,
      passed: 0,
      errors: [],
      warnings: [],
      info: [],
      details: {}
    };

    // Run all analysis rules
    for (const rule of this.analysisRules) {
      try {
        const result = rule.check(this.packageData);
        
        results.details[rule.id] = {
          name: rule.name,
          description: rule.description,
          severity: rule.severity,
          passed: result.passed,
          details: result.details
        };

        if (result.passed) {
          results.passed++;
        } else {
          const issue = {
            id: rule.id,
            name: rule.name,
            description: rule.description,
            details: result.details
          };

          switch (rule.severity) {
            case 'error':
              results.errors.push(issue);
              break;
            case 'warning':
              results.warnings.push(issue);
              break;
            case 'info':
              results.info.push(issue);
              break;
          }
        }
      } catch (error) {
        results.errors.push({
          id: rule.id,
          name: rule.name,
          description: `Analysis failed: ${error.message}`,
          details: 'Check failed'
        });
      }
    }

    // Calculate overall score and status
    results.score = Math.round((results.passed / results.totalChecks) * 100);
    
    if (results.errors.length === 0) {
      results.overall = results.warnings.length === 0 ? 'excellent' : 'good';
    } else {
      results.overall = results.errors.length <= 2 ? 'needs-improvement' : 'poor';
    }

    return results;
  }

  async analyzeSecurityIssues() {
    console.log('🔒 Analyzing security issues...\n');
    
    try {
      // Run npm audit and parse results
      const auditOutput = execSync('npm audit --json', { 
        encoding: 'utf-8',
        stdio: ['pipe', 'pipe', 'ignore'] // Suppress stderr
      });
      
      const auditData = JSON.parse(auditOutput);
      
      return {
        vulnerabilities: auditData.metadata?.vulnerabilities || {},
        advisories: Object.keys(auditData.advisories || {}),
        summary: {
          total: auditData.metadata?.totalDependencies || 0,
          vulnerablePackages: Object.keys(auditData.advisories || {}).length
        }
      };
    } catch (error) {
      // npm audit returns non-zero exit code when vulnerabilities found
      try {
        const auditOutput = error.stdout || error.message;
        if (auditOutput.includes('{')) {
          const auditData = JSON.parse(auditOutput);
          return {
            vulnerabilities: auditData.metadata?.vulnerabilities || {},
            advisories: Object.keys(auditData.advisories || {}),
            summary: {
              total: auditData.metadata?.totalDependencies || 0,
              vulnerablePackages: Object.keys(auditData.advisories || {}).length
            }
          };
        }
      } catch (parseError) {
        // Fall back to basic analysis
      }
      
      return {
        vulnerabilities: { info: 0, low: 0, moderate: 0, high: 0, critical: 0 },
        advisories: [],
        summary: { total: 0, vulnerablePackages: 0 },
        error: 'Could not analyze security issues'
      };
    }
  }

  async analyzeOutdatedPackages() {
    console.log('📅 Analyzing outdated packages...\n');
    
    try {
      // Check for outdated packages
      const outdatedOutput = execSync('npm outdated --json', {
        encoding: 'utf-8',
        stdio: ['pipe', 'pipe', 'ignore']
      });
      
      const outdatedData = JSON.parse(outdatedOutput || '{}');
      const outdatedCount = Object.keys(outdatedData).length;
      
      return {
        count: outdatedCount,
        packages: outdatedData,
        summary: outdatedCount > 0 ? `${outdatedCount} packages are outdated` : 'All packages up to date'
      };
    } catch (error) {
      return {
        count: 0,
        packages: {},
        summary: 'Could not check for outdated packages',
        error: error.message
      };
    }
  }

  generateReport(results, securityResults, outdatedResults) {
    let report = '# Package Quality Analysis Report\n\n';
    
    // Overall status
    const statusEmoji = {
      excellent: '🌟',
      good: '✅',
      'needs-improvement': '⚠️',
      poor: '❌'
    };
    
    report += `**Overall Quality:** ${statusEmoji[results.overall]} ${results.overall.toUpperCase()}\n`;
    report += `**Score:** ${results.score}/100\n`;
    report += `**Checks:** ${results.passed}/${results.totalChecks} passed\n\n`;

    // Package information
    report += `## 📦 Package Information\n\n`;
    report += `- **Name:** ${this.packageData.name}\n`;
    report += `- **Version:** ${this.packageData.version}\n`;
    report += `- **Description:** ${this.packageData.description || 'Not provided'}\n`;
    
    const depCount = Object.keys(this.packageData.dependencies || {}).length;
    const devDepCount = Object.keys(this.packageData.devDependencies || {}).length;
    report += `- **Dependencies:** ${depCount} production, ${devDepCount} development\n\n`;

    // Security analysis
    if (securityResults) {
      report += `## 🔒 Security Analysis\n\n`;
      const vulns = securityResults.vulnerabilities;
      const totalVulns = Object.values(vulns).reduce((sum, count) => sum + count, 0);
      
      if (totalVulns > 0) {
        report += `**Vulnerabilities Found:** ${totalVulns}\n`;
        if (vulns.critical > 0) report += `- 🚨 Critical: ${vulns.critical}\n`;
        if (vulns.high > 0) report += `- ⚠️ High: ${vulns.high}\n`;
        if (vulns.moderate > 0) report += `- 🟡 Moderate: ${vulns.moderate}\n`;
        if (vulns.low > 0) report += `- ℹ️ Low: ${vulns.low}\n`;
        report += `\n**Recommendation:** Run \`npm audit fix\` to address vulnerabilities.\n\n`;
      } else {
        report += `✅ No known vulnerabilities found.\n\n`;
      }
    }

    // Outdated packages
    if (outdatedResults) {
      report += `## 📅 Package Freshness\n\n`;
      if (outdatedResults.count > 0) {
        report += `⚠️ **${outdatedResults.count} packages are outdated**\n\n`;
        report += `**Recommendation:** Run \`npm update\` or \`npx npm-check-updates -u\` to update packages.\n\n`;
      } else {
        report += `✅ All packages are up to date.\n\n`;
      }
    }

    // Detailed results by severity
    if (results.errors.length > 0) {
      report += `## 🚨 Errors (${results.errors.length})\n\n`;
      results.errors.forEach(error => {
        report += `- **${error.id}**: ${error.name}\n`;
        report += `  ${error.details}\n\n`;
      });
    }

    if (results.warnings.length > 0) {
      report += `## ⚠️ Warnings (${results.warnings.length})\n\n`;
      results.warnings.forEach(warning => {
        report += `- **${warning.id}**: ${warning.name}\n`;
        report += `  ${warning.details}\n\n`;
      });
    }

    if (results.info.length > 0) {
      report += `## ℹ️ Suggestions (${results.info.length})\n\n`;
      results.info.forEach(info => {
        report += `- **${info.id}**: ${info.name}\n`;
        report += `  ${info.details}\n\n`;
      });
    }

    // Recommendations
    report += `## 📋 Recommendations\n\n`;
    
    if (results.overall === 'poor') {
      report += `1. **Critical**: Address all error-level issues immediately\n`;
      report += `2. **High Priority**: Fix security vulnerabilities\n`;
      report += `3. **Medium Priority**: Address warning-level issues\n`;
    } else if (results.overall === 'needs-improvement') {
      report += `1. Fix remaining error-level issues\n`;
      report += `2. Consider addressing warning-level issues\n`;
      report += `3. Keep packages updated regularly\n`;
    } else {
      report += `1. Maintain current quality standards\n`;
      report += `2. Regular dependency updates\n`;
      report += `3. Monitor for new security issues\n`;
    }

    return report;
  }

  async runCompleteAnalysis() {
    const packageResults = await this.analyzePackage();
    const securityResults = await this.analyzeSecurityIssues();
    const outdatedResults = await this.analyzeOutdatedPackages();

    const report = this.generateReport(packageResults, securityResults, outdatedResults);

    // Save report
    const reportPath = './package-quality-report.md';
    fs.writeFileSync(reportPath, report);

    console.log('📊 Package Quality Analysis Complete!\n');
    console.log(`Overall Quality: ${packageResults.overall.toUpperCase()}`);
    console.log(`Score: ${packageResults.score}/100`);
    console.log(`Errors: ${packageResults.errors.length}`);
    console.log(`Warnings: ${packageResults.warnings.length}`);
    console.log(`Security Issues: ${Object.values(securityResults.vulnerabilities || {}).reduce((sum, count) => sum + count, 0)}`);
    console.log(`Outdated Packages: ${outdatedResults.count}`);
    console.log(`\n📄 Detailed report saved: ${reportPath}`);

    return {
      packageResults,
      securityResults,
      outdatedResults,
      reportPath
    };
  }
}

// CLI interface
if (process.argv[1] === new URL(import.meta.url).pathname) {
  const args = process.argv.slice(2);
  const packagePath = args[0] || './package.json';

  const analyzer = new PackageQualityAnalyzer(packagePath);
  analyzer.runCompleteAnalysis().catch(console.error);
}

export { PackageQualityAnalyzer };