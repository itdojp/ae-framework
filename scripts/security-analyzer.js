#!/usr/bin/env node

/**
 * Security Analyzer
 * Comprehensive security analysis for ae-framework
 */

import { execSync } from 'child_process';
import { existsSync, readFileSync, writeFileSync, mkdirSync } from 'fs';
import { join, dirname } from 'path';
import { fileURLToPath } from 'url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = dirname(__filename);

class SecurityAnalyzer {
  constructor() {
    this.projectRoot = join(__dirname, '..');
    this.reportDir = join(this.projectRoot, 'security-reports');
    this.timestamp = new Date().toISOString().replace(/[:.]/g, '-');
  }

  async analyze() {
    console.log('🔐 Running comprehensive security analysis...\n');
    
    this.ensureReportDirectory();
    
    const results = {
      timestamp: new Date().toISOString(),
      summary: {
        totalChecks: 5,
        passed: 0,
        failed: 0,
        warnings: 0
      },
      checks: {
        secretsScan: await this.runSecretsScanning(),
        dependencyAudit: await this.runDependencyAudit(),
        codeqlAnalysis: await this.runCodeQLAnalysis(),
        sensitiveFileCheck: await this.checkSensitiveFiles(),
        securityPolicyCheck: await this.checkSecurityPolicies()
      }
    };

    // Calculate summary
    Object.values(results.checks).forEach(check => {
      if (check.status === 'passed') results.summary.passed++;
      else if (check.status === 'failed') results.summary.failed++;
      else if (check.status === 'warning') results.summary.warnings++;
    });

    // Generate report
    await this.generateReport(results);
    
    console.log('\n📊 Security Analysis Summary:');
    console.log(`✅ Passed: ${results.summary.passed}`);
    console.log(`❌ Failed: ${results.summary.failed}`);
    console.log(`⚠️  Warnings: ${results.summary.warnings}`);
    
    const overallScore = (results.summary.passed / results.summary.totalChecks) * 100;
    console.log(`🎯 Security Score: ${overallScore.toFixed(1)}%`);
    
    if (results.summary.failed > 0) {
      console.log('\n🚨 Security issues detected! Please review the report.');
      process.exit(1);
    }
    
    return results;
  }

  async runSecretsScanning() {
    console.log('🔍 Scanning for secrets and credentials...');
    
    try {
      // Run gitleaks
      const gitleaksResult = execSync('npx gitleaks detect --no-git --verbose', {
        cwd: this.projectRoot,
        encoding: 'utf-8',
        stdio: 'pipe'
      });
      
      console.log('  ✅ No secrets detected by gitleaks');
      
      // Additional manual patterns check
      const sensitivePatterns = [
        /password\s*=\s*["'][^"']{3,}["']/gi,
        /api[_-]?key\s*=\s*["'][^"']{10,}["']/gi,
        /secret\s*=\s*["'][^"']{8,}["']/gi,
        /token\s*=\s*["'][^"']{16,}["']/gi,
        /-----BEGIN\s+(RSA\s+)?PRIVATE\s+KEY-----/gi
      ];
      
      const findings = await this.scanForPatterns(sensitivePatterns);
      
      return {
        status: findings.length === 0 ? 'passed' : 'failed',
        tool: 'gitleaks + manual patterns',
        details: findings.length === 0 
          ? ['No secrets or credentials detected']
          : findings.map(f => `Found potential secret: ${f.file}:${f.line}`)
      };
      
    } catch (error) {
      if (error.status === 1) {
        // Gitleaks found secrets
        return {
          status: 'failed',
          tool: 'gitleaks',
          details: ['Secrets detected by gitleaks - check output above']
        };
      } else {
        return {
          status: 'warning',
          tool: 'gitleaks',
          details: [`Gitleaks scan failed: ${error.message}`]
        };
      }
    }
  }

  async runDependencyAudit() {
    console.log('📦 Auditing dependencies for vulnerabilities...');
    
    try {
      const auditResult = execSync('npm audit --audit-level=moderate --json', {
        cwd: this.projectRoot,
        encoding: 'utf-8',
        stdio: 'pipe'
      });
      
      const audit = JSON.parse(auditResult);
      
      if (audit.metadata.vulnerabilities.total === 0) {
        console.log('  ✅ No vulnerabilities found in dependencies');
        return {
          status: 'passed',
          tool: 'npm audit',
          details: ['No security vulnerabilities found in dependencies']
        };
      } else {
        const vulns = audit.metadata.vulnerabilities;
        console.log(`  ⚠️  Found ${vulns.total} vulnerabilities`);
        
        return {
          status: vulns.high > 0 || vulns.critical > 0 ? 'failed' : 'warning',
          tool: 'npm audit',
          details: [
            `Total vulnerabilities: ${vulns.total}`,
            `Critical: ${vulns.critical}, High: ${vulns.high}`,
            `Moderate: ${vulns.moderate}, Low: ${vulns.low}`
          ]
        };
      }
      
    } catch (error) {
      // npm audit returns non-zero exit code when vulnerabilities found
      try {
        const auditResult = error.stdout;
        const audit = JSON.parse(auditResult);
        const vulns = audit.metadata.vulnerabilities;
        
        return {
          status: vulns.high > 0 || vulns.critical > 0 ? 'failed' : 'warning',
          tool: 'npm audit',
          details: [
            `Total vulnerabilities: ${vulns.total}`,
            `Critical: ${vulns.critical}, High: ${vulns.high}`,
            `Moderate: ${vulns.moderate}, Low: ${vulns.low}`
          ]
        };
      } catch (parseError) {
        return {
          status: 'warning',
          tool: 'npm audit',
          details: [`Audit failed: ${error.message}`]
        };
      }
    }
  }

  async runCodeQLAnalysis() {
    console.log('🔬 Running CodeQL security analysis...');
    
    // Check if CodeQL is available
    try {
      execSync('which codeql', { stdio: 'pipe' });
    } catch {
      console.log('  ⚠️  CodeQL not installed - skipping analysis');
      return {
        status: 'warning',
        tool: 'CodeQL',
        details: ['CodeQL not installed - install from GitHub CLI for full analysis']
      };
    }

    try {
      // Create CodeQL database
      const dbPath = join(this.reportDir, 'codeql-db');
      execSync(`codeql database create ${dbPath} --language=javascript --source-root=${this.projectRoot}`, {
        cwd: this.projectRoot,
        stdio: 'pipe'
      });

      // Run security queries
      const resultsPath = join(this.reportDir, 'codeql-results.sarif');
      execSync(`codeql database analyze ${dbPath} --format=sarif-latest --output=${resultsPath}`, {
        cwd: this.projectRoot,
        stdio: 'pipe'
      });

      // Parse results
      const results = JSON.parse(readFileSync(resultsPath, 'utf-8'));
      const issues = results.runs[0].results || [];
      
      console.log(`  ✅ CodeQL analysis completed - ${issues.length} issues found`);
      
      return {
        status: issues.length === 0 ? 'passed' : 'warning',
        tool: 'CodeQL',
        details: issues.length === 0 
          ? ['No security issues detected by CodeQL']
          : [`Found ${issues.length} potential security issues - see SARIF report`]
      };
      
    } catch (error) {
      return {
        status: 'warning',
        tool: 'CodeQL',
        details: [`CodeQL analysis failed: ${error.message}`]
      };
    }
  }

  async checkSensitiveFiles() {
    console.log('📄 Checking for sensitive files...');
    
    const sensitiveFiles = [
      '.env',
      '.env.local',
      '.env.production',
      'config/secrets.json',
      'config/database.yml',
      'docker-compose.override.yml',
      'id_rsa',
      'id_rsa.pub',
      'credentials.json',
      'service-account-key.json'
    ];
    
    const foundFiles = [];
    for (const file of sensitiveFiles) {
      if (existsSync(join(this.projectRoot, file))) {
        foundFiles.push(file);
      }
    }
    
    // Check if sensitive files are in .gitignore
    const gitignorePath = join(this.projectRoot, '.gitignore');
    let gitignoreContent = '';
    if (existsSync(gitignorePath)) {
      gitignoreContent = readFileSync(gitignorePath, 'utf-8');
    }
    
    const unprotectedFiles = foundFiles.filter(file => 
      !gitignoreContent.includes(file) && !gitignoreContent.includes(file.split('/').pop())
    );
    
    console.log(`  ✅ Checked ${sensitiveFiles.length} potential sensitive file patterns`);
    
    return {
      status: unprotectedFiles.length === 0 ? 'passed' : 'failed',
      tool: 'File Scanner',
      details: unprotectedFiles.length === 0
        ? ['No unprotected sensitive files found']
        : [`Unprotected sensitive files: ${unprotectedFiles.join(', ')}`]
    };
  }

  async checkSecurityPolicies() {
    console.log('📋 Checking security policies and configurations...');
    
    const checks = [];
    
    // Check for SECURITY.md
    if (existsSync(join(this.projectRoot, 'SECURITY.md'))) {
      checks.push('✅ SECURITY.md file exists');
    } else {
      checks.push('❌ SECURITY.md file missing');
    }
    
    // Check package.json for security scripts
    const packageJsonPath = join(this.projectRoot, 'package.json');
    if (existsSync(packageJsonPath)) {
      const packageJson = JSON.parse(readFileSync(packageJsonPath, 'utf-8'));
      const scripts = packageJson.scripts || {};
      
      if (scripts['security:scan'] || scripts['security:audit']) {
        checks.push('✅ Security scripts configured');
      } else {
        checks.push('❌ No security scripts in package.json');
      }
      
      // Check for security-related dependencies
      const devDeps = packageJson.devDependencies || {};
      const securityTools = ['gitleaks', 'helmet', 'express-rate-limit', 'cors'];
      const installedTools = securityTools.filter(tool => 
        devDeps[tool] || (packageJson.dependencies && packageJson.dependencies[tool])
      );
      
      if (installedTools.length > 0) {
        checks.push(`✅ Security tools installed: ${installedTools.join(', ')}`);
      } else {
        checks.push('⚠️  No security tools detected in dependencies');
      }
    }
    
    // Check for GitHub security features
    const githubDir = join(this.projectRoot, '.github');
    if (existsSync(githubDir)) {
      const securityFiles = [
        'dependabot.yml',
        'workflows/security.yml',
        'workflows/codeql-analysis.yml'
      ];
      
      const existingFiles = securityFiles.filter(file => 
        existsSync(join(githubDir, file))
      );
      
      if (existingFiles.length > 0) {
        checks.push(`✅ GitHub security features: ${existingFiles.join(', ')}`);
      } else {
        checks.push('⚠️  No GitHub security workflows configured');
      }
    }
    
    const failedChecks = checks.filter(check => check.includes('❌'));
    
    return {
      status: failedChecks.length === 0 ? 'passed' : 'warning',
      tool: 'Policy Checker',
      details: checks
    };
  }

  async scanForPatterns(patterns) {
    const findings = [];
    const extensions = ['.js', '.ts', '.jsx', '.tsx', '.json', '.yml', '.yaml', '.env'];
    
    // Recursive file scan (simplified implementation)
    const scanDirectory = (dir) => {
      try {
        const files = execSync(`find ${dir} -type f \\( ${extensions.map(ext => `-name "*${ext}"`).join(' -o ')} \\) | head -1000`, {
          encoding: 'utf-8',
          cwd: this.projectRoot
        }).split('\n').filter(Boolean);
        
        for (const file of files) {
          if (file.includes('node_modules') || file.includes('.git')) continue;
          
          try {
            const content = readFileSync(file, 'utf-8');
            const lines = content.split('\n');
            
            for (let i = 0; i < lines.length; i++) {
              for (const pattern of patterns) {
                if (pattern.test(lines[i])) {
                  findings.push({
                    file: file.replace(this.projectRoot + '/', ''),
                    line: i + 1,
                    pattern: pattern.toString()
                  });
                }
              }
            }
          } catch (error) {
            // Skip files that can't be read
          }
        }
      } catch (error) {
        console.warn(`Warning: Could not scan directory ${dir}: ${error.message}`);
      }
    };
    
    scanDirectory(this.projectRoot);
    return findings;
  }

  ensureReportDirectory() {
    if (!existsSync(this.reportDir)) {
      mkdirSync(this.reportDir, { recursive: true });
    }
  }

  async generateReport(results) {
    const reportPath = join(this.reportDir, `security-report-${this.timestamp}.json`);
    writeFileSync(reportPath, JSON.stringify(results, null, 2));
    
    // Generate human-readable report
    const htmlReport = this.generateHTMLReport(results);
    const htmlPath = join(this.reportDir, `security-report-${this.timestamp}.html`);
    writeFileSync(htmlPath, htmlReport);
    
    console.log(`\n📋 Security report generated:`);
    console.log(`   JSON: ${reportPath}`);
    console.log(`   HTML: ${htmlPath}`);
  }

  generateHTMLReport(results) {
    return `<!DOCTYPE html>
<html>
<head>
    <title>Security Analysis Report</title>
    <style>
        body { font-family: Arial, sans-serif; margin: 40px; }
        .header { background: #f8f9fa; padding: 20px; border-radius: 8px; }
        .summary { display: flex; gap: 20px; margin: 20px 0; }
        .metric { padding: 15px; border-radius: 8px; text-align: center; }
        .passed { background: #d4edda; color: #155724; }
        .failed { background: #f8d7da; color: #721c24; }
        .warning { background: #fff3cd; color: #856404; }
        .check { margin: 20px 0; padding: 15px; border-left: 4px solid #ccc; }
        .check.passed { border-color: #28a745; }
        .check.failed { border-color: #dc3545; }
        .check.warning { border-color: #ffc107; }
        .details { margin: 10px 0; }
        .details li { margin: 5px 0; }
    </style>
</head>
<body>
    <div class="header">
        <h1>🔐 Security Analysis Report</h1>
        <p>Generated: ${results.timestamp}</p>
        <p>Overall Score: ${((results.summary.passed / results.summary.totalChecks) * 100).toFixed(1)}%</p>
    </div>
    
    <div class="summary">
        <div class="metric passed">
            <h3>${results.summary.passed}</h3>
            <p>Passed</p>
        </div>
        <div class="metric failed">
            <h3>${results.summary.failed}</h3>
            <p>Failed</p>
        </div>
        <div class="metric warning">
            <h3>${results.summary.warnings}</h3>
            <p>Warnings</p>
        </div>
    </div>
    
    <h2>Security Checks</h2>
    ${Object.entries(results.checks).map(([name, check]) => `
        <div class="check ${check.status}">
            <h3>${name} (${check.tool})</h3>
            <p><strong>Status:</strong> ${check.status.toUpperCase()}</p>
            <div class="details">
                <ul>
                    ${check.details.map(detail => `<li>${detail}</li>`).join('')}
                </ul>
            </div>
        </div>
    `).join('')}
</body>
</html>`;
  }
}

// CLI execution
if (import.meta.url === `file://${process.argv[1]}`) {
  const analyzer = new SecurityAnalyzer();
  analyzer.analyze().catch(error => {
    console.error('Security analysis failed:', error);
    process.exit(1);
  });
}

export { SecurityAnalyzer };