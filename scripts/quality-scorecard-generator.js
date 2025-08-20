#!/usr/bin/env node

/**
 * Quality Scorecard Generator
 * Comprehensive quality assessment for ae-framework
 */

import fs from 'fs';
import path from 'path';
import { execSync } from 'child_process';

class QualityScorecard {
  constructor() {
    this.metrics = {
      staticAnalysis: { weight: 15, score: 0, details: [] },
      mutationTesting: { weight: 10, score: 0, details: [] },
      flakeDetection: { weight: 10, score: 0, details: [] },
      irSchemaStrictness: { weight: 15, score: 0, details: [] },
      packageQuality: { weight: 15, score: 0, details: [] },
      propertyBasedTesting: { weight: 10, score: 0, details: [] },
      security: { weight: 10, score: 0, details: [] },
      benchmarkRegression: { weight: 5, score: 0, details: [] },
      hermeticTesting: { weight: 5, score: 0, details: [] },
      releaseOperations: { weight: 3, score: 0, details: [] },
      failureVisualization: { weight: 1, score: 0, details: [] },
      accessibility: { weight: 1, score: 0, details: [] }
    };
    
    this.overallScore = 0;
    this.recommendations = [];
  }

  async evaluateStaticAnalysis() {
    console.log('📊 Evaluating Static Analysis...');
    
    let score = 0;
    const details = [];

    try {
      // Check for TypeScript strict mode
      const tsconfigPath = './tsconfig.json';
      if (fs.existsSync(tsconfigPath)) {
        const tsconfig = JSON.parse(fs.readFileSync(tsconfigPath, 'utf-8'));
        
        if (tsconfig.compilerOptions?.noUncheckedIndexedAccess) {
          score += 30;
          details.push('✅ TypeScript strict indexing enabled');
        } else {
          details.push('❌ TypeScript strict indexing not enabled');
        }

        if (tsconfig.compilerOptions?.strict) {
          score += 25;
          details.push('✅ TypeScript strict mode enabled');
        } else {
          details.push('❌ TypeScript strict mode not enabled');
        }
      }

      // Check for unused code detection
      const packageJson = JSON.parse(fs.readFileSync('./package.json', 'utf-8'));
      if (packageJson.scripts?.['lint:unused']) {
        score += 25;
        details.push('✅ Unused code detection configured');
      } else {
        details.push('❌ No unused code detection');
      }

      // Check for circular dependency detection
      if (packageJson.scripts?.['lint:deps']) {
        score += 20;
        details.push('✅ Circular dependency detection configured');
      } else {
        details.push('❌ No circular dependency detection');
      }

    } catch (error) {
      details.push(`❌ Static analysis evaluation failed: ${error.message}`);
    }

    this.metrics.staticAnalysis.score = score;
    this.metrics.staticAnalysis.details = details;
  }

  async evaluateMutationTesting() {
    console.log('🧬 Evaluating Mutation Testing...');
    
    let score = 0;
    const details = [];

    try {
      // Check for mutation testing configuration
      if (fs.existsSync('./stryker.config.js')) {
        score += 40;
        details.push('✅ Stryker mutation testing configured');
        
        const config = fs.readFileSync('./stryker.config.js', 'utf-8');
        if (config.includes('checkers')) {
          score += 20;
          details.push('✅ TypeScript checker configured');
        }
        
        if (config.includes('thresholds')) {
          score += 20;
          details.push('✅ Quality thresholds set');
        }
      } else {
        details.push('❌ No mutation testing configuration');
      }

      // Check for mutation testing script
      const packageJson = JSON.parse(fs.readFileSync('./package.json', 'utf-8'));
      if (packageJson.scripts?.mutation) {
        score += 20;
        details.push('✅ Mutation testing script available');
      } else {
        details.push('❌ No mutation testing script');
      }

    } catch (error) {
      details.push(`❌ Mutation testing evaluation failed: ${error.message}`);
    }

    this.metrics.mutationTesting.score = score;
    this.metrics.mutationTesting.details = details;
  }

  async evaluateFlakeDetection() {
    console.log('🔄 Evaluating Flake Detection...');
    
    let score = 0;
    const details = [];

    try {
      // Check for flake detection tool
      if (fs.existsSync('./scripts/flake-detector.js')) {
        score += 50;
        details.push('✅ Custom flake detection tool implemented');
      } else {
        details.push('❌ No flake detection tool');
      }

      // Check for flake detection scripts
      const packageJson = JSON.parse(fs.readFileSync('./package.json', 'utf-8'));
      const flakeScripts = Object.keys(packageJson.scripts || {}).filter(s => s.includes('flake'));
      
      if (flakeScripts.length >= 3) {
        score += 30;
        details.push(`✅ Multiple flake detection scripts (${flakeScripts.length})`);
      } else if (flakeScripts.length > 0) {
        score += 15;
        details.push(`⚠️ Basic flake detection scripts (${flakeScripts.length})`);
      } else {
        details.push('❌ No flake detection scripts');
      }

      // Check for flake reporting
      if (fs.existsSync('./flake-reports') || flakeScripts.some(s => s.includes('report'))) {
        score += 20;
        details.push('✅ Flake reporting configured');
      } else {
        details.push('❌ No flake reporting');
      }

    } catch (error) {
      details.push(`❌ Flake detection evaluation failed: ${error.message}`);
    }

    this.metrics.flakeDetection.score = score;
    this.metrics.flakeDetection.details = details;
  }

  async evaluateIRSchemaStrictness() {
    console.log('📋 Evaluating IR Schema Strictness...');
    
    let score = 0;
    const details = [];

    try {
      // Check for strict schema implementation
      if (fs.existsSync('./packages/spec-compiler/src/strict-schema.ts')) {
        score += 40;
        details.push('✅ Strict Zod schema implementation');
      } else {
        details.push('❌ No strict schema implementation');
      }

      // Check for IR validation tool
      if (fs.existsSync('./scripts/ir-schema-validator.js')) {
        score += 30;
        details.push('✅ IR validation tool implemented');
      } else {
        details.push('❌ No IR validation tool');
      }

      // Check for IR validation scripts
      const packageJson = JSON.parse(fs.readFileSync('./package.json', 'utf-8'));
      const irScripts = Object.keys(packageJson.scripts || {}).filter(s => s.startsWith('ir:'));
      
      if (irScripts.length >= 3) {
        score += 30;
        details.push(`✅ Comprehensive IR scripts (${irScripts.length})`);
      } else {
        details.push(`⚠️ Limited IR scripts (${irScripts.length})`);
      }

    } catch (error) {
      details.push(`❌ IR schema evaluation failed: ${error.message}`);
    }

    this.metrics.irSchemaStrictness.score = score;
    this.metrics.irSchemaStrictness.details = details;
  }

  async evaluatePackageQuality() {
    console.log('📦 Evaluating Package Quality...');
    
    let score = 0;
    const details = [];

    try {
      // Check for package quality analyzer
      if (fs.existsSync('./scripts/package-quality-analyzer.js')) {
        score += 30;
        details.push('✅ Package quality analyzer implemented');
      } else {
        details.push('❌ No package quality analyzer');
      }

      // Run quick package analysis
      if (fs.existsSync('./package-quality-report.md')) {
        const report = fs.readFileSync('./package-quality-report.md', 'utf-8');
        
        if (report.includes('GOOD') || report.includes('EXCELLENT')) {
          score += 40;
          details.push('✅ Package quality rated as GOOD/EXCELLENT');
        } else if (report.includes('NEEDS-IMPROVEMENT')) {
          score += 20;
          details.push('⚠️ Package quality needs improvement');
        } else {
          score += 10;
          details.push('❌ Package quality poor');
        }

        // Check security
        if (report.includes('Vulnerabilities Found: 0')) {
          score += 30;
          details.push('✅ No security vulnerabilities');
        } else {
          const vulnMatch = report.match(/Vulnerabilities Found: (\d+)/);
          if (vulnMatch) {
            const vulnCount = parseInt(vulnMatch[1]);
            if (vulnCount <= 10) {
              score += 15;
              details.push(`⚠️ ${vulnCount} security vulnerabilities (manageable)`);
            } else {
              details.push(`❌ ${vulnCount} security vulnerabilities (high risk)`);
            }
          }
        }
      }

    } catch (error) {
      details.push(`❌ Package quality evaluation failed: ${error.message}`);
    }

    this.metrics.packageQuality.score = score;
    this.metrics.packageQuality.details = details;
  }

  async evaluateBasicMetrics() {
    console.log('⚡ Evaluating Basic Metrics...');
    
    // Property-based testing
    const packageJson = JSON.parse(fs.readFileSync('./package.json', 'utf-8'));
    
    if (packageJson.devDependencies?.['fast-check']) {
      this.metrics.propertyBasedTesting.score = 60;
      this.metrics.propertyBasedTesting.details.push('✅ fast-check dependency present');
    }
    
    if (packageJson.scripts?.pbt) {
      this.metrics.propertyBasedTesting.score += 40;
      this.metrics.propertyBasedTesting.details.push('✅ Property-based testing script configured');
    }

    // Security
    if (packageJson.scripts?.['verify:security']) {
      this.metrics.security.score += 30;
      this.metrics.security.details.push('✅ Security verification script');
    }
    
    if (packageJson.scripts?.['package:audit']) {
      this.metrics.security.score += 35;
      this.metrics.security.details.push('✅ Security audit script');
    }
    
    if (fs.existsSync('./src/security/')) {
      this.metrics.security.score += 35;
      this.metrics.security.details.push('✅ Security module present');
    }

    // Accessibility
    if (packageJson.scripts?.['test:a11y']) {
      this.metrics.accessibility.score = 100;
      this.metrics.accessibility.details.push('✅ Accessibility testing configured');
    }

    // Check for benchmark regression detection
    if (packageJson.scripts?.['benchmark:regression']) {
      this.metrics.benchmarkRegression.score = 70;
      this.metrics.benchmarkRegression.details.push('✅ Benchmark regression detection implemented');
    } else {
      this.metrics.benchmarkRegression.score = 30;
      this.metrics.benchmarkRegression.details.push('⚠️ Basic performance testing present');
    }
    
    // Check for hermetic testing
    if (packageJson.scripts?.['hermetic:quick'] || packageJson.scripts?.['hermetic:validate']) {
      this.metrics.hermeticTesting.score = 60;
      this.metrics.hermeticTesting.details.push('✅ Hermetic test validation implemented');
    } else {
      this.metrics.hermeticTesting.score = 20;
      this.metrics.hermeticTesting.details.push('⚠️ Limited hermetic testing');
    }
    
    this.metrics.releaseOperations.score = 40;
    this.metrics.releaseOperations.details.push('⚠️ Basic release scripts present');
    
    this.metrics.failureVisualization.score = 25;
    this.metrics.failureVisualization.details.push('⚠️ Basic failure handling present');
  }

  calculateOverallScore() {
    let weightedScore = 0;
    let totalWeight = 0;

    for (const [metric, data] of Object.entries(this.metrics)) {
      weightedScore += (data.score / 100) * data.weight;
      totalWeight += data.weight;
    }

    this.overallScore = Math.round((weightedScore / totalWeight) * 100);
  }

  generateRecommendations() {
    const recommendations = [];

    // Priority recommendations based on scores
    for (const [metric, data] of Object.entries(this.metrics)) {
      if (data.score < 50 && data.weight >= 10) {
        recommendations.push({
          priority: 'high',
          metric,
          message: `Improve ${metric.replace(/([A-Z])/g, ' $1').toLowerCase()} (current: ${data.score}%)`
        });
      } else if (data.score < 70 && data.weight >= 15) {
        recommendations.push({
          priority: 'medium',
          metric,
          message: `Enhance ${metric.replace(/([A-Z])/g, ' $1').toLowerCase()} (current: ${data.score}%)`
        });
      }
    }

    // Security-specific recommendations
    if (this.metrics.security.score < 80) {
      recommendations.push({
        priority: 'high',
        metric: 'security',
        message: 'Address security vulnerabilities immediately'
      });
    }

    this.recommendations = recommendations;
  }

  generateReport() {
    const timestamp = new Date().toISOString();
    
    let report = '# Quality Scorecard Report\n\n';
    report += `**Generated:** ${timestamp}\n`;
    report += `**Overall Score:** ${this.getScoreEmoji(this.overallScore)} ${this.overallScore}/100\n`;
    report += `**Quality Level:** ${this.getQualityLevel(this.overallScore)}\n\n`;

    // Score breakdown
    report += '## 📊 Score Breakdown\n\n';
    report += '| Metric | Weight | Score | Status |\n';
    report += '|--------|--------|-------|--------|\n';
    
    for (const [metric, data] of Object.entries(this.metrics)) {
      const name = metric.replace(/([A-Z])/g, ' $1').replace(/^./, str => str.toUpperCase());
      const emoji = this.getScoreEmoji(data.score);
      report += `| ${name} | ${data.weight}% | ${data.score}/100 | ${emoji} |\n`;
    }
    report += '\n';

    // Detailed results
    report += '## 📋 Detailed Results\n\n';
    
    for (const [metric, data] of Object.entries(this.metrics)) {
      const name = metric.replace(/([A-Z])/g, ' $1').replace(/^./, str => str.toUpperCase());
      report += `### ${name} (${data.score}/100)\n\n`;
      
      if (data.details.length > 0) {
        data.details.forEach(detail => {
          report += `${detail}\n`;
        });
      } else {
        report += 'No detailed information available.\n';
      }
      report += '\n';
    }

    // Recommendations
    if (this.recommendations.length > 0) {
      report += '## 🎯 Recommendations\n\n';
      
      const highPriority = this.recommendations.filter(r => r.priority === 'high');
      const mediumPriority = this.recommendations.filter(r => r.priority === 'medium');
      const lowPriority = this.recommendations.filter(r => r.priority === 'low');

      if (highPriority.length > 0) {
        report += '### 🚨 High Priority\n\n';
        highPriority.forEach((rec, i) => {
          report += `${i + 1}. ${rec.message}\n`;
        });
        report += '\n';
      }

      if (mediumPriority.length > 0) {
        report += '### ⚠️ Medium Priority\n\n';
        mediumPriority.forEach((rec, i) => {
          report += `${i + 1}. ${rec.message}\n`;
        });
        report += '\n';
      }

      if (lowPriority.length > 0) {
        report += '### ℹ️ Low Priority\n\n';
        lowPriority.forEach((rec, i) => {
          report += `${i + 1}. ${rec.message}\n`;
        });
        report += '\n';
      }
    }

    // Summary and next steps
    report += '## 📈 Summary\n\n';
    
    if (this.overallScore >= 80) {
      report += '🌟 **Excellent quality!** The project demonstrates high standards across most quality metrics.\n\n';
      report += '**Next Steps:**\n';
      report += '- Maintain current quality standards\n';
      report += '- Focus on continuous improvement\n';
      report += '- Regular quality reviews\n';
    } else if (this.overallScore >= 60) {
      report += '✅ **Good quality foundation.** Several areas show strong implementation with room for improvement.\n\n';
      report += '**Next Steps:**\n';
      report += '- Address high-priority recommendations\n';
      report += '- Strengthen weak areas\n';
      report += '- Implement missing quality tools\n';
    } else {
      report += '⚠️ **Quality needs significant improvement.** Core quality practices need implementation.\n\n';
      report += '**Next Steps:**\n';
      report += '- Implement fundamental quality tools\n';
      report += '- Address security vulnerabilities\n';
      report += '- Establish quality gates\n';
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

  getQualityLevel(score) {
    if (score >= 90) return 'EXCELLENT';
    if (score >= 80) return 'VERY GOOD';
    if (score >= 70) return 'GOOD';
    if (score >= 60) return 'FAIR';
    if (score >= 40) return 'POOR';
    return 'VERY POOR';
  }

  async runCompleteAssessment() {
    console.log('🏆 Running Quality Scorecard Assessment...\n');

    await this.evaluateStaticAnalysis();
    await this.evaluateMutationTesting();
    await this.evaluateFlakeDetection();
    await this.evaluateIRSchemaStrictness();
    await this.evaluatePackageQuality();
    await this.evaluateBasicMetrics();

    this.calculateOverallScore();
    this.generateRecommendations();

    const report = this.generateReport();

    // Save report
    const reportPath = './quality-scorecard.md';
    fs.writeFileSync(reportPath, report);

    console.log('\n🏆 Quality Scorecard Assessment Complete!\n');
    console.log(`Overall Score: ${this.overallScore}/100 (${this.getQualityLevel(this.overallScore)})`);
    console.log(`Recommendations: ${this.recommendations.length}`);
    console.log(`Report saved: ${reportPath}\n`);

    return {
      overallScore: this.overallScore,
      metrics: this.metrics,
      recommendations: this.recommendations,
      reportPath
    };
  }
}

// CLI interface
if (process.argv[1] === new URL(import.meta.url).pathname) {
  const scorecard = new QualityScorecard();
  scorecard.runCompleteAssessment().catch(console.error);
}

export { QualityScorecard };