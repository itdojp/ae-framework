#!/usr/bin/env node

/**
 * Performance Budget Validator
 * Validates performance metrics against configured budgets
 */

const fs = require('fs');
const path = require('path');
const { performance } = require('perf_hooks');

class PerformanceBudgetValidator {
  constructor(configPath = './config/performance-budgets.json') {
    this.configPath = configPath;
    this.config = this.loadConfig();
    this.environment = process.env.NODE_ENV || 'ci';
    this.results = {
      timestamp: new Date().toISOString(),
      environment: this.environment,
      violations: [],
      metrics: {},
      summary: {
        total: 0,
        passed: 0,
        failed: 0,
        warnings: 0
      }
    };
  }

  loadConfig() {
    try {
      const configData = fs.readFileSync(this.configPath, 'utf8');
      return JSON.parse(configData);
    } catch (error) {
      console.error(`❌ Failed to load budget configuration: ${error.message}`);
      process.exit(1);
    }
  }

  getEnvironmentBudget(budgetValue) {
    const envConfig = this.config.environments[this.environment];
    if (!envConfig) return budgetValue;
    return budgetValue * (envConfig.toleranceMultiplier || 1.0);
  }

  measureMemoryUsage() {
    const memUsage = process.memoryUsage();
    return {
      heapUsed: memUsage.heapUsed,
      heapTotal: memUsage.heapTotal,
      external: memUsage.external,
      rss: memUsage.rss
    };
  }

  measureCpuUsage() {
    return new Promise((resolve) => {
      const startUsage = process.cpuUsage();
      const startTime = process.hrtime();

      setTimeout(() => {
        const endUsage = process.cpuUsage(startUsage);
        const endTime = process.hrtime(startTime);
        
        const userTime = endUsage.user / 1000000; // Convert to seconds
        const systemTime = endUsage.system / 1000000;
        const totalTime = (endTime[0] * 1000000000 + endTime[1]) / 1000000000;
        
        const cpuPercent = (userTime + systemTime) / totalTime;
        resolve(Math.min(cpuPercent, 1.0));
      }, 100);
    });
  }

  async validateSystemBudgets() {
    console.log('🔍 Validating system performance budgets...');
    
    const systemBudgets = this.config.budgets.system;
    
    // Memory budget validation
    const memoryMetrics = this.measureMemoryUsage();
    const memoryBudget = this.getEnvironmentBudget(systemBudgets.memory.value);
    
    this.results.metrics.memory = memoryMetrics.heapUsed;
    this.validateMetric('memory', memoryMetrics.heapUsed, memoryBudget, systemBudgets.memory);

    // CPU budget validation
    const cpuUsage = await this.measureCpuUsage();
    const cpuBudget = this.getEnvironmentBudget(systemBudgets.cpu.value);
    
    this.results.metrics.cpu = cpuUsage;
    this.validateMetric('cpu', cpuUsage, cpuBudget, systemBudgets.cpu);
  }

  async validateTestBudgets() {
    console.log('🧪 Validating test performance budgets...');
    
    const testBudgets = this.config.budgets.tests;
    
    // Simulate test execution measurement
    const testStart = performance.now();
    await new Promise(resolve => setTimeout(resolve, 100)); // Simulate test work
    const testDuration = performance.now() - testStart;
    
    const executionBudget = this.getEnvironmentBudget(testBudgets.execution.value);
    this.results.metrics.testExecution = testDuration;
    this.validateMetric('testExecution', testDuration, executionBudget, testBudgets.execution);
  }

  validateApplicationBudgets() {
    console.log('🚀 Validating application performance budgets...');
    
    const appBudgets = this.config.budgets.application;
    
    // Bundle size validation (mock)
    const mockBundleSize = 1.8 * 1024 * 1024; // 1.8MB mock
    const bundleBudget = this.getEnvironmentBudget(appBudgets.bundleSize.value);
    
    this.results.metrics.bundleSize = mockBundleSize;
    this.validateMetric('bundleSize', mockBundleSize, bundleBudget, appBudgets.bundleSize);
  }

  validateMetric(name, actualValue, budgetValue, config) {
    this.results.summary.total++;
    
    const violation = {
      metric: name,
      actual: actualValue,
      budget: budgetValue,
      unit: config.unit,
      description: config.description,
      severity: config.severity,
      passed: actualValue <= budgetValue,
      ratio: actualValue / budgetValue
    };

    if (violation.passed) {
      this.results.summary.passed++;
      console.log(`  ✅ ${name}: ${this.formatValue(actualValue, config.unit)} (budget: ${this.formatValue(budgetValue, config.unit)})`);
    } else {
      if (config.severity === 'error') {
        this.results.summary.failed++;
        console.log(`  ❌ ${name}: ${this.formatValue(actualValue, config.unit)} exceeds budget ${this.formatValue(budgetValue, config.unit)}`);
      } else {
        this.results.summary.warnings++;
        console.log(`  ⚠️  ${name}: ${this.formatValue(actualValue, config.unit)} exceeds budget ${this.formatValue(budgetValue, config.unit)} (${config.severity})`);
      }
      this.results.violations.push(violation);
    }
  }

  formatValue(value, unit) {
    switch (unit) {
      case 'bytes':
        return `${Math.round(value / 1024 / 1024 * 10) / 10}MB`;
      case 'ms':
        return `${Math.round(value)}ms`;
      case 'percentage':
        return `${Math.round(value * 100)}%`;
      default:
        return `${value}${unit}`;
    }
  }

  async validate() {
    console.log(`📊 Performance Budget Validation (Environment: ${this.environment})`);
    console.log('=' .repeat(60));
    
    try {
      await this.validateSystemBudgets();
      await this.validateTestBudgets();
      this.validateApplicationBudgets();
      
      this.generateReport();
      this.printSummary();
      
      return this.results.summary.failed === 0;
    } catch (error) {
      console.error(`❌ Validation failed: ${error.message}`);
      return false;
    }
  }

  generateReport() {
    if (!this.config.reporting.enabled) return;

    const reportDir = path.dirname(this.config.reporting.outputPath);
    if (!fs.existsSync(reportDir)) {
      fs.mkdirSync(reportDir, { recursive: true });
    }

    fs.writeFileSync(
      this.config.reporting.outputPath,
      JSON.stringify(this.results, null, 2)
    );
    
    console.log(`📄 Report saved to: ${this.config.reporting.outputPath}`);
  }

  printSummary() {
    console.log('=' .repeat(60));
    console.log('📋 SUMMARY');
    console.log(`Total checks: ${this.results.summary.total}`);
    console.log(`✅ Passed: ${this.results.summary.passed}`);
    console.log(`❌ Failed: ${this.results.summary.failed}`);
    console.log(`⚠️  Warnings: ${this.results.summary.warnings}`);
    
    if (this.results.violations.length > 0) {
      console.log('\n🚨 BUDGET VIOLATIONS:');
      this.results.violations.forEach(v => {
        const icon = v.severity === 'error' ? '❌' : '⚠️';
        console.log(`${icon} ${v.metric}: ${this.formatValue(v.actual, v.unit)} / ${this.formatValue(v.budget, v.unit)} (${Math.round(v.ratio * 100)}%)`);
      });
    }
    
    console.log('=' .repeat(60));
  }
}

// CLI execution
async function main() {
  const args = process.argv.slice(2);
  const configPath = args.includes('--config') ? args[args.indexOf('--config') + 1] : undefined;
  
  const validator = new PerformanceBudgetValidator(configPath);
  const success = await validator.validate();
  
  process.exit(success ? 0 : 1);
}

if (require.main === module) {
  main().catch(error => {
    console.error('❌ Validation error:', error);
    process.exit(1);
  });
}

module.exports = { PerformanceBudgetValidator };