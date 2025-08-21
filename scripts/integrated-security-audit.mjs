#!/usr/bin/env node

/**
 * Integrated Security & Compliance Audit System
 * Combines security analysis, dependency auditing, compliance checking,
 * and vulnerability assessment into a unified monitoring solution
 */

import fs from 'fs';
import fsp from 'fs/promises';
import path from 'path';
import { spawn, execSync, spawnSync } from 'child_process';
import { pathToFileURL } from 'url';

class IntegratedSecurityAuditor {
  constructor(options = {}) {
    this.projectRoot = process.cwd();
    this.reportsDir = './reports/security-audit';
    this.tempDir = './temp-reports/security-analysis';
    this.timestamp = new Date().toISOString().replace(/[:.]/g, '-');
    
    this.options = {
      enableDependencyAudit: options.enableDependencyAudit ?? true,
      enableSecretsScanning: options.enableSecretsScanning ?? true,
      enableComplianceCheck: options.enableComplianceCheck ?? true,
      enableVulnerabilityAssessment: options.enableVulnerabilityAssessment ?? true,
      enableCodeAnalysis: options.enableCodeAnalysis ?? true,
      generateDetailedReport: options.generateDetailedReport ?? true,
      ...options
    };

    this.auditResults = {
      timestamp: new Date().toISOString(),
      environment: {
        nodeVersion: process.version,
        platform: process.platform,
        isCI: process.env.CI === 'true'
      },
      summary: {
        totalChecks: 0,
        passed: 0,
        failed: 0,
        warnings: 0,
        criticalIssues: 0,
        riskScore: 0
      },
      audits: {},
      recommendations: [],
      actionItems: []
    };
  }

  async ensureDirectories() {
    console.log('📁 Setting up security audit environment...');
    
    const dirs = [
      this.reportsDir,
      this.tempDir,
      './temp-reports/dependency-analysis',
      './temp-reports/vulnerability-scans',
      './temp-reports/compliance-checks'
    ];

    for (const dir of dirs) {
      if (!fs.existsSync(dir)) {
        await fsp.mkdir(dir, { recursive: true });
        console.log(`   ✅ Created: ${dir}`);
      }
    }
  }

  async runDependencyAudit() {
    if (!this.options.enableDependencyAudit) return { status: 'skipped', reason: 'Disabled by options' };

    console.log('📦 Running dependency security audit...');
    
    const audit = {
      status: 'passed',
      vulnerabilities: [],
      outdatedPackages: [],
      recommendations: [],
      details: {}
    };

    let npmAudit, npmOutdated;
    
    try {
      // NPM Audit
      try {
        npmAudit = spawnSync('npm', ['audit', '--json'], {
          encoding: 'utf8',
          timeout: 30000,
          cwd: this.projectRoot
        });
        if (npmAudit.error) {
          throw npmAudit.error;
        }
        if (npmAudit.status !== 0 && !npmAudit.stdout) {
          throw new Error(`npm audit failed: ${npmAudit.stderr}`);
        }
        const npmAuditResult = npmAudit.stdout;
        
        let npmData;
        try {
          npmData = JSON.parse(npmAuditResult);
        } catch (parseError) {
          console.error('❌ Failed to parse npm audit JSON output:', parseError.message);
          audit.status = 'error';
          audit.details.npm = { error: 'Malformed JSON from npm audit', rawOutput: npmAuditResult };
          audit.recommendations.push('Check your npm version and network connectivity. Try running `npm audit` manually to diagnose the issue.');
          return audit;
        }
        audit.details.npm = npmData;
        
        if (npmData.vulnerabilities) {
          Object.entries(npmData.vulnerabilities).forEach(([pkg, vuln]) => {
            const severity = vuln.severity || 'unknown';
            audit.vulnerabilities.push({
              package: pkg,
              severity: severity,
              range: vuln.range,
              via: vuln.via,
              fixAvailable: vuln.fixAvailable
            });
            
            if (['critical', 'high'].includes(severity)) {
              this.auditResults.summary.criticalIssues++;
              audit.status = 'failed';
            } else if (severity === 'moderate') {
              audit.status = audit.status === 'passed' ? 'warning' : audit.status;
            }
          });
        }
        
        console.log(`   📊 Found ${audit.vulnerabilities.length} dependency vulnerabilities`);
        
      } catch (error) {
        if (error.message && error.message.includes('npm audit failed') && npmAudit && npmAudit.stdout) {
          // npm audit found vulnerabilities, parse the output
          try {
            const npmData = JSON.parse(npmAudit.stdout);
            audit.details.npm = npmData;
            audit.status = 'warning';
            console.log('   ⚠️ NPM audit found issues (parsed from error output)');
          } catch (parseError) {
            console.warn(`   ⚠️ NPM audit error: ${error.message}`);
            audit.status = 'warning';
            audit.details.npm = { error: error.message };
          }
        } else {
          throw error;
        }
      }

      // Check for outdated packages
      try {
        npmOutdated = spawnSync('npm', ['outdated', '--json'], {
          encoding: 'utf8',
          timeout: 20000,
          cwd: this.projectRoot
        });
        
        if (npmOutdated.stdout) {
          const outdatedData = JSON.parse(npmOutdated.stdout);
          audit.details.outdated = outdatedData;
          
          Object.entries(outdatedData).forEach(([pkg, info]) => {
            audit.outdatedPackages.push({
              package: pkg,
              current: info.current,
              wanted: info.wanted,
              latest: info.latest,
              location: info.location
            });
          });
        }
      } catch (error) {
        // npm outdated returns non-zero exit code when packages are outdated
        if (npmOutdated && npmOutdated.stdout) {
          try {
            const outdatedData = JSON.parse(npmOutdated.stdout);
            audit.details.outdated = outdatedData;
            console.log(`   📈 Found ${Object.keys(outdatedData).length} outdated packages`);
          } catch (parseError) {
            console.log('   ℹ️ No outdated packages or unable to parse npm outdated output');
          }
        }
      }

      // Generate recommendations
      if (audit.vulnerabilities.length > 0) {
        audit.recommendations.push(`Run 'npm audit fix' to automatically fix ${audit.vulnerabilities.filter(v => v.fixAvailable).length} vulnerabilities`);
        
        const criticalVulns = audit.vulnerabilities.filter(v => v.severity === 'critical');
        if (criticalVulns.length > 0) {
          audit.recommendations.push(`CRITICAL: ${criticalVulns.length} critical vulnerabilities require immediate attention`);
        }
      }
      
      if (audit.outdatedPackages.length > 0) {
        audit.recommendations.push(`Consider updating ${audit.outdatedPackages.length} outdated packages`);
      }

    } catch (error) {
      console.error(`   ❌ Dependency audit failed: ${error.message}`);
      audit.status = 'failed';
      audit.details.error = error.message;
    }

    return audit;
  }

  async runSecretsScanning() {
    if (!this.options.enableSecretsScanning) return { status: 'skipped', reason: 'Disabled by options' };

    console.log('🔍 Scanning for exposed secrets and credentials...');
    
    const scan = {
      status: 'passed',
      findings: [],
      patterns: [],
      recommendations: [],
      details: {}
    };

    try {
      // Define secret detection patterns
      const secretPatterns = [
        { name: 'API Keys', pattern: /(?:api[_-]?key|apikey)\s*[:=]\s*['"]\w{20,}['"]/, severity: 'high' },
        { name: 'AWS Access Keys', pattern: /AKIA[0-9A-Z]{16}/, severity: 'critical' },
        { name: 'Private Keys', pattern: /-----BEGIN\s+(?:RSA\s+)?PRIVATE\s+KEY-----/, severity: 'critical' },
        { name: 'Database URLs', pattern: /(?:mongodb|mysql|postgres):\/\/[^\s"'`<>]+/, severity: 'high' },
        { name: 'JWT Tokens', pattern: /eyJ[A-Za-z0-9-_=]+\.[A-Za-z0-9-_=]+\.?[A-Za-z0-9-_.+/=]*/, severity: 'medium' },
        { name: 'Generic Secrets', pattern: /(?:secret|password|token|key)\s*[:=]\s*['"]\w{16,}['"]/, severity: 'medium' }
      ];

      scan.patterns = secretPatterns.map(p => ({ name: p.name, severity: p.severity }));

      // Scan common file types
      const filesToScan = [
        '.env*',
        '*.js',
        '*.ts',
        '*.json',
        '*.yaml',
        '*.yml',
        '*.md',
        '*.txt'
      ];

      const { glob } = await import('glob');
      
      for (const pattern of filesToScan) {
        try {
          const files = await glob(pattern, { 
            cwd: this.projectRoot,
            ignore: [
              'node_modules/**',
              'dist/**',
              'build/**',
              '.git/**',
              'coverage/**',
              'temp-reports/**',
              'reports/**'
            ]
          });

          for (const file of files) {
            try {
              const content = fs.readFileSync(file, 'utf8');
              
              for (const secretPattern of secretPatterns) {
                const matches = content.match(new RegExp(secretPattern.pattern, 'gi'));
                if (matches) {
                  const lines = content.split('\n');
                  matches.forEach(match => {
                    const lineNumber = lines.findIndex(line => line.includes(match)) + 1;
                    
                    scan.findings.push({
                      file: file,
                      line: lineNumber,
                      type: secretPattern.name,
                      severity: secretPattern.severity,
                      preview: match.substring(0, 50) + (match.length > 50 ? '...' : ''),
                      recommendation: this.getSecretRecommendation(secretPattern.name)
                    });

                    if (secretPattern.severity === 'critical') {
                      this.auditResults.summary.criticalIssues++;
                      scan.status = 'failed';
                    } else if (secretPattern.severity === 'high') {
                      scan.status = scan.status === 'passed' ? 'warning' : scan.status;
                    }
                  });
                }
              }
            } catch (readError) {
              // Skip binary files or files that can't be read
            }
          }
        } catch (globError) {
          console.warn(`   ⚠️ Could not scan pattern ${pattern}: ${globError.message}`);
        }
      }

      console.log(`   🔍 Scanned files, found ${scan.findings.length} potential secrets`);

      // Generate recommendations
      if (scan.findings.length > 0) {
        scan.recommendations.push('Remove hardcoded secrets and use environment variables');
        scan.recommendations.push('Implement proper secrets management (e.g., Azure Key Vault, AWS Secrets Manager)');
        scan.recommendations.push('Add secrets scanning to pre-commit hooks');
        
        const criticalFindings = scan.findings.filter(f => f.severity === 'critical');
        if (criticalFindings.length > 0) {
          scan.recommendations.push(`URGENT: ${criticalFindings.length} critical secrets must be rotated immediately`);
        }
      }

    } catch (error) {
      console.error(`   ❌ Secrets scanning failed: ${error.message}`);
      scan.status = 'failed';
      scan.details.error = error.message;
    }

    return scan;
  }

  getSecretRecommendation(secretType) {
    const recommendations = {
      'API Keys': 'Store in environment variables or secure key management service',
      'AWS Access Keys': 'Use IAM roles or store in AWS Secrets Manager',
      'Private Keys': 'Store in secure key vault and never commit to repository',
      'Database URLs': 'Use environment variables for connection strings',
      'JWT Tokens': 'Generate tokens dynamically, never hardcode',
      'Generic Secrets': 'Use environment variables or configuration management'
    };
    
    return recommendations[secretType] || 'Store securely and avoid hardcoding';
  }

  async runComplianceCheck() {
    if (!this.options.enableComplianceCheck) return { status: 'skipped', reason: 'Disabled by options' };

    console.log('📋 Running compliance and policy checks...');
    
    const compliance = {
      status: 'passed',
      policies: [],
      violations: [],
      recommendations: [],
      details: {}
    };

    try {
      // Check for security policy files
      const policyFiles = [
        'SECURITY.md',
        'security.md',
        '.github/SECURITY.md',
        'CODE_OF_CONDUCT.md',
        'CONTRIBUTING.md'
      ];

      const foundPolicies = [];
      for (const policyFile of policyFiles) {
        if (fs.existsSync(policyFile)) {
          foundPolicies.push(policyFile);
        }
      }

      compliance.policies = foundPolicies;
      
      if (foundPolicies.length === 0) {
        compliance.violations.push({
          type: 'Missing Security Policy',
          severity: 'medium',
          description: 'No security policy documentation found',
          recommendation: 'Create SECURITY.md with vulnerability reporting process'
        });
        compliance.status = 'warning';
      }

      // Check package.json for security-related configurations
      if (fs.existsSync('package.json')) {
        const packageJson = JSON.parse(fs.readFileSync('package.json', 'utf8'));
        
        // Check for security-related scripts
        const securityScripts = Object.keys(packageJson.scripts || {}).filter(script => 
          script.includes('security') || script.includes('audit') || script.includes('vulnerability')
        );
        
        compliance.details.securityScripts = securityScripts;
        
        if (securityScripts.length === 0) {
          compliance.violations.push({
            type: 'Missing Security Scripts',
            severity: 'low',
            description: 'No security-related npm scripts found',
            recommendation: 'Add security audit scripts to package.json'
          });
        }

        // Check for known vulnerable package patterns
        const allDeps = { ...packageJson.dependencies, ...packageJson.devDependencies };
        const suspiciousPatterns = ['eval', 'serialize', 'unserialize'];
        
        Object.keys(allDeps).forEach(dep => {
          if (suspiciousPatterns.some(pattern => dep.includes(pattern))) {
            compliance.violations.push({
              type: 'Potentially Risky Dependency',
              severity: 'medium',
              description: `Package '${dep}' may pose security risks`,
              recommendation: `Review and audit the '${dep}' package for security implications`
            });
          }
        });
      }

      // Check for common security files
      const securityFiles = [
        '.gitignore',
        '.npmignore',
        '.dockerignore'
      ];

      const missingSecurityFiles = [];
      for (const secFile of securityFiles) {
        if (!fs.existsSync(secFile)) {
          missingSecurityFiles.push(secFile);
        }
      }

      if (missingSecurityFiles.length > 0) {
        compliance.violations.push({
          type: 'Missing Security Configuration Files',
          severity: 'medium',
          description: `Missing files: ${missingSecurityFiles.join(', ')}`,
          recommendation: 'Create proper ignore files to prevent sensitive data exposure'
        });
      }

      // Check for OPA compliance (if available)
      const opaResultsPath = './reports/opa-results.json';
      if (fs.existsSync(opaResultsPath)) {
        const opaResults = JSON.parse(fs.readFileSync(opaResultsPath, 'utf8'));
        compliance.details.opa = opaResults;
        
        if (opaResults.violations && opaResults.violations.length > 0) {
          compliance.violations.push({
            type: 'OPA Policy Violations',
            severity: 'high',
            description: `${opaResults.violations.length} policy violations found`,
            recommendation: 'Review and fix OPA policy violations'
          });
          compliance.status = 'failed';
        }
      }

      console.log(`   📋 Found ${compliance.policies.length} policy files, ${compliance.violations.length} violations`);

      // Generate recommendations
      compliance.recommendations = compliance.violations.map(v => v.recommendation);
      if (compliance.recommendations.length === 0) {
        compliance.recommendations.push('Compliance checks passed - maintain current security posture');
      }

    } catch (error) {
      console.error(`   ❌ Compliance check failed: ${error.message}`);
      compliance.status = 'failed';
      compliance.details.error = error.message;
    }

    return compliance;
  }

  async runVulnerabilityAssessment() {
    if (!this.options.enableVulnerabilityAssessment) return { status: 'skipped', reason: 'Disabled by options' };

    console.log('🛡️ Running vulnerability assessment...');
    
    const assessment = {
      status: 'passed',
      vulnerabilities: [],
      riskScore: 0,
      recommendations: [],
      details: {}
    };

    try {
      // Check for common vulnerability patterns in code
      const vulnerabilityPatterns = [
        { name: 'SQL Injection', pattern: /(?:query|execute)\s*\(\s*['"]\s*SELECT.*\+.*['"]/, severity: 'critical', category: 'injection' },
        { name: 'XSS Risk', pattern: /innerHTML\s*=.*\+/, severity: 'high', category: 'xss' },
        { name: 'Path Traversal', pattern: /fs\.readFile.*\.\./g, severity: 'high', category: 'path-traversal' },
        { name: 'Insecure Randomness', pattern: /Math\.random\(\)/g, severity: 'medium', category: 'weak-crypto' },
        { name: 'Eval Usage', pattern: /\beval\s*\(/g, severity: 'critical', category: 'code-injection' },
        { name: 'Hardcoded Crypto', pattern: /(?:createHash|createCipher).*['"]\w+['"]/, severity: 'medium', category: 'crypto' }
      ];

      const { glob } = await import('glob');
      const codeFiles = await glob('**/*.{js,ts}', { 
        cwd: this.projectRoot,
        ignore: [
          'node_modules/**',
          'dist/**',
          'build/**',
          'coverage/**',
          'temp-reports/**',
          'reports/**'
        ]
      });

      for (const file of codeFiles) {
        try {
          const content = fs.readFileSync(file, 'utf8');
          
          for (const vulnPattern of vulnerabilityPatterns) {
            const matches = content.match(vulnPattern.pattern);
            if (matches) {
              const lines = content.split('\n');
              matches.forEach(match => {
                const lineNumber = lines.findIndex(line => line.includes(match)) + 1;
                
                assessment.vulnerabilities.push({
                  file: file,
                  line: lineNumber,
                  type: vulnPattern.name,
                  severity: vulnPattern.severity,
                  category: vulnPattern.category,
                  preview: match.substring(0, 100) + (match.length > 100 ? '...' : ''),
                  recommendation: this.getVulnerabilityRecommendation(vulnPattern.category)
                });

                // Update risk score
                const riskPoints = { critical: 10, high: 7, medium: 4, low: 1 };
                assessment.riskScore += riskPoints[vulnPattern.severity] || 0;

                if (vulnPattern.severity === 'critical') {
                  this.auditResults.summary.criticalIssues++;
                  assessment.status = 'failed';
                } else if (vulnPattern.severity === 'high') {
                  assessment.status = assessment.status === 'passed' ? 'warning' : assessment.status;
                }
              });
            }
          }
        } catch (readError) {
          // Skip files that can't be read
        }
      }

      console.log(`   🛡️ Scanned ${codeFiles.length} files, found ${assessment.vulnerabilities.length} potential vulnerabilities`);

      // Generate recommendations based on findings
      if (assessment.vulnerabilities.length > 0) {
        const categories = [...new Set(assessment.vulnerabilities.map(v => v.category))];
        categories.forEach(category => {
          assessment.recommendations.push(this.getVulnerabilityRecommendation(category));
        });
        
        assessment.recommendations.push('Implement static code analysis tools in CI/CD pipeline');
        assessment.recommendations.push('Conduct regular security code reviews');
      }

      // Risk score interpretation
      assessment.details.riskInterpretation = this.interpretRiskScore(assessment.riskScore);

    } catch (error) {
      console.error(`   ❌ Vulnerability assessment failed: ${error.message}`);
      assessment.status = 'failed';
      assessment.details.error = error.message;
    }

    return assessment;
  }

  getVulnerabilityRecommendation(category) {
    const recommendations = {
      'injection': 'Use parameterized queries and input validation',
      'xss': 'Sanitize user input and use templating engines with auto-escaping',
      'path-traversal': 'Validate and sanitize file paths, use allowlist approach',
      'weak-crypto': 'Use cryptographically secure random number generators',
      'code-injection': 'Avoid eval() and similar functions, use safer alternatives',
      'crypto': 'Use well-established cryptographic libraries and standards'
    };
    
    return recommendations[category] || 'Follow security best practices for this vulnerability type';
  }

  interpretRiskScore(score) {
    if (score === 0) return { level: 'very-low', description: 'No significant security risks detected' };
    if (score <= 5) return { level: 'low', description: 'Minor security concerns identified' };
    if (score <= 15) return { level: 'medium', description: 'Moderate security risks require attention' };
    if (score <= 30) return { level: 'high', description: 'Significant security risks need immediate action' };
    return { level: 'critical', description: 'Critical security vulnerabilities require urgent remediation' };
  }

  async runCodeAnalysis() {
    if (!this.options.enableCodeAnalysis) return { status: 'skipped', reason: 'Disabled by options' };

    console.log('🔬 Running security-focused code analysis...');
    
    const analysis = {
      status: 'passed',
      findings: [],
      metrics: {},
      recommendations: [],
      details: {}
    };

    try {
      // Run ESLint with security rules if available
      try {
        const eslintOutput = execSync('npx eslint . --format json', { 
          encoding: 'utf8',
          timeout: 30000,
          cwd: this.projectRoot 
        });
        
        const eslintResults = JSON.parse(eslintOutput);
        const securityIssues = eslintResults.filter(result => 
          result.messages.some(msg => 
            msg.ruleId && (
              msg.ruleId.includes('security') || 
              msg.ruleId.includes('no-eval') ||
              msg.ruleId.includes('no-implied-eval')
            )
          )
        );
        
        analysis.details.eslint = {
          totalFiles: eslintResults.length,
          securityIssues: securityIssues.length,
          results: securityIssues
        };
        
        console.log(`   🔬 ESLint found ${securityIssues.length} security-related issues`);
        
      } catch (eslintError) {
        console.log('   ℹ️ ESLint not available or no security rules configured');
        analysis.details.eslint = { error: 'ESLint not available' };
      }

      // Analyze code complexity and potential security hotspots
      const { glob } = await import('glob');
      const jsFiles = await glob('**/*.{js,ts}', { 
        cwd: this.projectRoot,
        ignore: ['node_modules/**', 'dist/**', 'build/**', 'coverage/**']
      });

      let totalLines = 0;
      let functionsCount = 0;
      let complexFunctions = 0;

      for (const file of jsFiles) {
        try {
          const content = fs.readFileSync(file, 'utf8');
          const lines = content.split('\n');
          totalLines += lines.length;
          
          // Count functions
          const functionMatches = content.match(/(?:function\s+\w+|const\s+\w+\s*=.*(?:=>|function))/g);
          if (functionMatches) {
            functionsCount += functionMatches.length;
            
            // Identify complex functions (simple heuristic)
            functionMatches.forEach(func => {
              const complexity = (func.match(/if|for|while|switch|catch/g) || []).length;
              if (complexity > 5) {
                complexFunctions++;
                analysis.findings.push({
                  file: file,
                  type: 'High Complexity Function',
                  severity: 'low',
                  description: `Function has complexity score of ${complexity}`,
                  recommendation: 'Consider refactoring complex functions for better security review'
                });
              }
            });
          }
        } catch (readError) {
          // Skip files that can't be read
        }
      }

      analysis.metrics = {
        totalLines,
        totalFiles: jsFiles.length,
        functionsCount,
        complexFunctions,
        averageLinesPerFile: Math.round(totalLines / jsFiles.length)
      };

      console.log(`   📊 Analyzed ${jsFiles.length} files (${totalLines} lines), ${complexFunctions} complex functions`);

      // Generate recommendations
      if (complexFunctions > 0) {
        analysis.recommendations.push(`Review ${complexFunctions} complex functions for security implications`);
      }
      
      analysis.recommendations.push('Implement automated security testing in CI/CD');
      analysis.recommendations.push('Regular code reviews with security focus');

    } catch (error) {
      console.error(`   ❌ Code analysis failed: ${error.message}`);
      analysis.status = 'failed';
      analysis.details.error = error.message;
    }

    return analysis;
  }

  async generateComprehensiveReport() {
    if (!this.options.generateDetailedReport) return null;

    console.log('📊 Generating comprehensive security audit report...');

    // Calculate final summary
    const audits = Object.values(this.auditResults.audits);
    this.auditResults.summary.totalChecks = audits.length;
    
    audits.forEach(audit => {
      if (audit.status === 'passed') this.auditResults.summary.passed++;
      else if (audit.status === 'failed') this.auditResults.summary.failed++;
      else if (audit.status === 'warning') this.auditResults.summary.warnings++;
    });

    // Calculate overall risk score
    const vulnAssessment = this.auditResults.audits.vulnerabilityAssessment;
    if (vulnAssessment && vulnAssessment.riskScore) {
      this.auditResults.summary.riskScore = vulnAssessment.riskScore;
    }

    // Consolidate recommendations
    const allRecommendations = new Set();
    audits.forEach(audit => {
      if (audit.recommendations) {
        audit.recommendations.forEach(rec => allRecommendations.add(rec));
      }
    });
    
    this.auditResults.recommendations = Array.from(allRecommendations);

    // Generate action items based on findings
    this.generateActionItems();

    // Save detailed report
    const reportPath = path.join(this.reportsDir, `security-audit-${this.timestamp}.json`);
    await fsp.writeFile(reportPath, JSON.stringify(this.auditResults, null, 2));

    // Generate human-readable summary
    const summaryPath = path.join(this.reportsDir, `security-summary-${this.timestamp}.md`);
    const summary = this.generateMarkdownSummary();
    await fsp.writeFile(summaryPath, summary);

    console.log(`   📄 Detailed report: ${reportPath}`);
    console.log(`   📋 Summary report: ${summaryPath}`);

    return this.auditResults;
  }

  generateActionItems() {
    const { audits, summary } = this.auditResults;

    // Critical issues need immediate attention
    if (summary.criticalIssues > 0) {
      this.auditResults.actionItems.push({
        priority: 'critical',
        action: `Address ${summary.criticalIssues} critical security issues immediately`,
        deadline: 'Within 24 hours'
      });
    }

    // Failed audits need remediation
    if (summary.failed > 0) {
      this.auditResults.actionItems.push({
        priority: 'high',
        action: `Fix ${summary.failed} failed security checks`,
        deadline: 'Within 1 week'
      });
    }

    // Warnings need review
    if (summary.warnings > 0) {
      this.auditResults.actionItems.push({
        priority: 'medium',
        action: `Review ${summary.warnings} security warnings`,
        deadline: 'Within 2 weeks'
      });
    }

    // Specific audit recommendations
    if (audits.dependencyAudit && audits.dependencyAudit.vulnerabilities?.length > 0) {
      this.auditResults.actionItems.push({
        priority: 'high',
        action: 'Update vulnerable dependencies',
        deadline: 'Within 3 days'
      });
    }

    if (audits.secretsScanning && audits.secretsScanning.findings?.length > 0) {
      this.auditResults.actionItems.push({
        priority: 'critical',
        action: 'Remove hardcoded secrets and rotate exposed credentials',
        deadline: 'Immediately'
      });
    }
  }

  generateMarkdownSummary() {
    const { summary, audits, recommendations, actionItems } = this.auditResults;
    
    return `# Security Audit Report

Generated: ${this.auditResults.timestamp}

## Executive Summary

| Metric | Value |
|--------|-------|
| Total Security Checks | ${summary.totalChecks} |
| Passed | ✅ ${summary.passed} |
| Failed | ❌ ${summary.failed} |
| Warnings | ⚠️ ${summary.warnings} |
| Critical Issues | 🚨 ${summary.criticalIssues} |
| Risk Score | ${summary.riskScore} |

## Audit Results

${Object.entries(audits).map(([name, audit]) => `
### ${name.replace(/([A-Z])/g, ' $1').toLowerCase().replace(/^./, str => str.toUpperCase())}
- **Status**: ${audit.status === 'passed' ? '✅ Passed' : audit.status === 'failed' ? '❌ Failed' : '⚠️ Warning'}
${audit.vulnerabilities ? `- **Vulnerabilities**: ${audit.vulnerabilities.length}` : ''}
${audit.findings ? `- **Findings**: ${audit.findings.length}` : ''}
${audit.violations ? `- **Violations**: ${audit.violations.length}` : ''}
`).join('')}

## Action Items

${actionItems.length > 0 ? actionItems.map(item => `
### ${item.priority.toUpperCase()} Priority
- **Action**: ${item.action}
- **Deadline**: ${item.deadline}
`).join('') : 'No immediate action items required.'}

## Recommendations

${recommendations.map(rec => `- 💡 ${rec}`).join('\n')}

## Next Steps

1. **Immediate**: Address all critical security issues
2. **Short-term**: Fix failed checks and high-priority vulnerabilities
3. **Medium-term**: Review warnings and implement preventive measures
4. **Long-term**: Establish continuous security monitoring

---
*Generated by Integrated Security Audit System*
`;
  }

  async displaySummary() {
    const { summary, audits } = this.auditResults;
    
    console.log('\n📋 Security Audit Summary:');
    console.log(`   🔍 Total Checks: ${summary.totalChecks}`);
    console.log(`   ✅ Passed: ${summary.passed}`);
    console.log(`   ❌ Failed: ${summary.failed}`);
    console.log(`   ⚠️ Warnings: ${summary.warnings}`);
    console.log(`   🚨 Critical Issues: ${summary.criticalIssues}`);
    console.log(`   📊 Risk Score: ${summary.riskScore}`);
    
    if (summary.criticalIssues > 0) {
      console.log(`\n🚨 CRITICAL: ${summary.criticalIssues} critical security issues require immediate attention!`);
    }
    
    console.log(`\n📁 Reports saved to: ${this.reportsDir}/`);
  }

  async run() {
    const startTime = Date.now();
    
    try {
      console.log('🔐 Starting integrated security & compliance audit...\n');
      
      await this.ensureDirectories();
      
      // Run all audit modules
      this.auditResults.audits.dependencyAudit = await this.runDependencyAudit();
      this.auditResults.audits.secretsScanning = await this.runSecretsScanning();
      this.auditResults.audits.complianceCheck = await this.runComplianceCheck();
      this.auditResults.audits.vulnerabilityAssessment = await this.runVulnerabilityAssessment();
      this.auditResults.audits.codeAnalysis = await this.runCodeAnalysis();
      
      const report = await this.generateComprehensiveReport();
      
      const executionTime = Date.now() - startTime;
      
      await this.displaySummary();
      
      console.log('\n✅ Security audit completed successfully!');
      console.log(`⏱️ Total execution time: ${executionTime}ms`);
      
      return {
        auditResults: this.auditResults,
        report,
        executionTime
      };
      
    } catch (error) {
      console.error(`❌ Security audit failed: ${error.message}`);
      console.error(error.stack);
      throw error;
    }
  }
}

// CLI execution
async function main() {
  const args = process.argv.slice(2);
  const options = {};
  
  // Parse command line arguments
  for (let i = 0; i < args.length; i++) {
    switch (args[i]) {
      case '--no-deps':
        options.enableDependencyAudit = false;
        break;
      case '--no-secrets':
        options.enableSecretsScanning = false;
        break;
      case '--no-compliance':
        options.enableComplianceCheck = false;
        break;
      case '--no-vulnerabilities':
        options.enableVulnerabilityAssessment = false;
        break;
      case '--no-code-analysis':
        options.enableCodeAnalysis = false;
        break;
      case '--no-reports':
        options.generateDetailedReport = false;
        break;
      case '--help':
        console.log(`
Integrated Security & Compliance Audit System

Usage: node integrated-security-audit.mjs [options]

Options:
  --no-deps              Disable dependency audit
  --no-secrets           Disable secrets scanning
  --no-compliance        Disable compliance checks
  --no-vulnerabilities   Disable vulnerability assessment
  --no-code-analysis     Disable code analysis
  --no-reports           Disable detailed report generation
  --help                 Show this help message

Audit Modules:
  • Dependency Security Audit: NPM vulnerabilities and outdated packages
  • Secrets Scanning: Exposed credentials and API keys
  • Compliance Checking: Security policies and best practices
  • Vulnerability Assessment: Code-level security issues
  • Code Analysis: Security-focused static analysis
        `);
        process.exit(0);
    }
  }
  
  const auditor = new IntegratedSecurityAuditor(options);
  const results = await auditor.run();
  
  // Exit with error code if critical issues found
  if (results.auditResults.summary.criticalIssues > 0) {
    console.log('\n💥 Exiting with error code due to critical security issues');
    process.exit(1);
  }
  
  if (results.auditResults.summary.failed > 0) {
    console.log('\n⚠️ Exiting with warning code due to failed security checks');
    process.exit(2);
  }
}

if (import.meta.url === pathToFileURL(process.argv[1]).href) {
  main().catch(error => {
    console.error('💥 Audit failed:', error.message);
    process.exit(1);
  });
}

export { IntegratedSecurityAuditor };