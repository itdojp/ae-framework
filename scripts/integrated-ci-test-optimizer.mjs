#!/usr/bin/env node

/**
 * Integrated CI/Test Optimization System
 * Combines stability enhancement, flake detection, and performance optimization
 * for comprehensive test environment improvement
 */

import fs from 'fs';
import fsp from 'fs/promises';
import path from 'path';
import { spawn, execSync } from 'child_process';
import { pathToFileURL } from 'url';

class IntegratedCITestOptimizer {
  constructor(options = {}) {
    this.isCI = process.env.CI === 'true';
    this.projectRoot = process.cwd();
    this.configDir = './config';
    this.reportsDir = './reports/ci-optimization';
    this.options = {
      enableFlakeDetection: options.enableFlakeDetection ?? true,
      enableStabilityEnhancement: options.enableStabilityEnhancement ?? true,
      enablePerformanceOptimization: options.enablePerformanceOptimization ?? true,
      generateReports: options.generateReports ?? true,
      ...options
    };
    
    this.config = this.loadConfig();
    this.metrics = {
      testsRun: 0,
      testsPass: 0,
      testsFail: 0,
      flakeTests: new Set(),
      performanceIssues: new Map(),
      optimizationsApplied: [],
      executionTime: 0,
      memoryUsage: new Map()
    };
  }

  loadConfig() {
    const defaultConfig = {
      stability: {
        retrySettings: {
          maxRetries: 3,
          retryDelay: 2000,
          exponentialBackoff: true
        },
        timeouts: {
          testTimeout: this.isCI ? 120000 : 60000,
          hookTimeout: this.isCI ? 60000 : 30000,
          teardownTimeout: 30000
        },
        resourceLimits: {
          maxConcurrency: this.isCI ? 2 : 4,
          memoryLimit: this.isCI ? '1GB' : '2GB',
          cpuLimit: this.isCI ? 1 : 2
        },
        environmentOptimizations: {
          disableAnimations: this.isCI,
          reducedLogging: this.isCI,
          skipLongRunningTests: false,
          enableStrictCleanup: true
        }
      },
      flakeDetection: {
        threshold: 0.05, // 5% failure rate
        earlyWarningThreshold: 0.15, // 15% for warnings
        minimumRuns: 5,
        analysisWindow: 10,
        patterns: {
          timeoutKeywords: ['timeout', 'timed out', 'exceeded', 'hang'],
          resourceKeywords: ['memory', 'leak', 'handle', 'worker', 'process'],
          concurrencyKeywords: ['race', 'concurrent', 'parallel', 'async'],
          environmentKeywords: ['CI', 'environment', 'platform', 'node_modules']
        }
      },
      performance: {
        slowTestThreshold: 10000, // 10 seconds
        memoryLeakThreshold: 100 * 1024 * 1024, // 100MB
        parallelization: {
          enabled: true,
          maxWorkers: this.isCI ? 2 : 4,
          chunkSize: 10
        },
        optimization: {
          enableTestCaching: true,
          enableSmartRetries: true,
          enableResourceMonitoring: true
        }
      }
    };

    try {
      const configPath = path.join(this.configDir, 'ci-test-optimization.json');
      if (fs.existsSync(configPath)) {
        const userConfig = JSON.parse(fs.readFileSync(configPath, 'utf8'));
        return this.mergeConfig(defaultConfig, userConfig);
      }
    } catch (error) {
      console.warn(`Warning: Could not load config: ${error.message}`);
    }

    return defaultConfig;
  }

  mergeConfig(defaultConfig, userConfig) {
    const merged = { ...defaultConfig };
    for (const [key, value] of Object.entries(userConfig)) {
      if (typeof value === 'object' && !Array.isArray(value)) {
        merged[key] = { ...merged[key], ...value };
      } else {
        merged[key] = value;
      }
    }
    return merged;
  }

  async ensureDirectories() {
    console.log('📁 Setting up optimization environment...');
    
    const dirs = [
      this.configDir,
      this.reportsDir,
      './temp-reports/ci-optimization',
      './temp-reports/flake-detection',
      './temp-reports/performance-analysis'
    ];

    for (const dir of dirs) {
      if (!fs.existsSync(dir)) {
        await fsp.mkdir(dir, { recursive: true });
        console.log(`   ✅ Created: ${dir}`);
      }
    }
  }

  async analyzeTestEnvironment() {
    console.log('🔍 Analyzing test environment...');
    
    const analysis = {
      nodeVersion: process.version,
      platform: process.platform,
      architecture: process.arch,
      memoryAvailable: Math.round(process.memoryUsage().heapTotal / 1024 / 1024) + 'MB',
      isCI: this.isCI,
      testFiles: [],
      configFiles: [],
      dependencies: {}
    };

    // Find test files
    try {
      const testPatterns = [
        'tests/**/*.test.ts',
        'tests/**/*.test.js',
        'src/**/*.test.ts',
        'src/**/*.test.js',
        '**/*.spec.ts',
        '**/*.spec.js'
      ];

      for (const pattern of testPatterns) {
        try {
          let glob;
          try {
            ({ glob } = await import('glob'));
          } catch (importError) {
            if (importError && importError.code === 'ERR_MODULE_NOT_FOUND') {
              throw new Error(
                "The 'glob' package is required to analyze test files but is not installed. Please run 'npm install glob' or 'yarn add glob'."
              );
            } else {
              throw importError;
            }
          }
          const files = await glob(pattern, { 
            cwd: this.projectRoot,
            ignore: ['node_modules/**', 'dist/**', 'build/**']
          });
          analysis.testFiles.push(...files);
        } catch (error) {
          if (error && error.message && error.message.includes("The 'glob' package is required")) {
            throw error; // propagate to outer catch for user visibility
          }
          // Pattern not found or other error, continue
        }
      }
    } catch (error) {
      console.warn(`Warning: Could not analyze test files: ${error.message}`);
    }

    // Check package.json for test-related dependencies
    try {
      const packageJsonPath = path.join(this.projectRoot, 'package.json');
      if (fs.existsSync(packageJsonPath)) {
        const packageJson = JSON.parse(fs.readFileSync(packageJsonPath, 'utf8'));
        const allDeps = { 
          ...packageJson.dependencies, 
          ...packageJson.devDependencies 
        };
        
        analysis.dependencies = Object.keys(allDeps).filter(dep => 
          dep.includes('test') || 
          dep.includes('jest') || 
          dep.includes('vitest') || 
          dep.includes('mocha') ||
          dep.includes('cypress') ||
          dep.includes('playwright')
        ).reduce((acc, dep) => {
          acc[dep] = allDeps[dep];
          return acc;
        }, {});
      }
    } catch (error) {
      console.warn(`Warning: Could not analyze dependencies: ${error.message}`);
    }

    console.log(`   📊 Found ${analysis.testFiles.length} test files`);
    console.log(`   🔧 Test frameworks detected: ${Object.keys(analysis.dependencies).join(', ') || 'none'}`);
    
    return analysis;
  }

  async optimizeVitestConfiguration() {
    if (!this.options.enableStabilityEnhancement) return null;
    
    console.log('⚙️ Optimizing Vitest configuration...');
    
    const vitestConfig = {
      test: {
        // Environment-specific timeouts
        testTimeout: this.config.stability.timeouts.testTimeout,
        hookTimeout: this.config.stability.timeouts.hookTimeout,
        teardownTimeout: this.config.stability.timeouts.teardownTimeout,
        
        // Resource optimization
        pool: 'threads',
        poolOptions: {
          threads: {
            maxThreads: this.config.stability.resourceLimits.maxConcurrency,
            minThreads: 1
          }
        },
        
        // Enhanced cleanup and isolation
        restoreMocks: true,
        clearMocks: true,
        resetMocks: true,
        resetModules: true,
        isolate: true,
        
        // CI-specific configuration
        reporter: this.isCI ? ['verbose', 'junit', 'json'] : ['verbose'],
        outputFile: this.isCI ? {
          junit: './reports/junit-results.xml',
          json: './reports/test-results.json'
        } : undefined,
        
        // Environment variables
        env: {
          NODE_ENV: 'test',
          CI: this.isCI ? 'true' : 'false',
          TEST_TIMEOUT: this.config.stability.timeouts.testTimeout.toString(),
          DISABLE_ANIMATIONS: this.config.stability.environmentOptimizations.disableAnimations.toString()
        },
        
        // Smart retry configuration
        retry: this.isCI ? this.config.stability.retrySettings.maxRetries : 1,
        
        // Performance monitoring
        logHeapUsage: this.config.performance.optimization.enableResourceMonitoring,
        
        // Coverage configuration for stability
        coverage: {
          enabled: !this.isCI || this.config.performance.optimization.enableTestCaching,
          provider: 'v8',
          reporter: ['text', 'json', 'html'],
          exclude: [
            'node_modules/**',
            'dist/**',
            'coverage/**',
            'tests/**',
            '**/*.test.*',
            '**/*.spec.*'
          ]
        },

        // Test exclusion patterns for known flaky tests
        exclude: [
          'tests/**/*.flaky.test.*',
          'tests/**/flaky/**',
          'node_modules/**'
        ]
      }
    };

    // Apply additional optimizations for CI
    if (this.isCI) {
      vitestConfig.test.maxWorkers = this.config.performance.parallelization.maxWorkers;
      vitestConfig.test.minWorkers = 1;
      vitestConfig.test.singleThread = this.config.stability.resourceLimits.maxConcurrency === 1;
    }

    // Save optimized configuration
    const configPath = './vitest.optimized.config.ts';
    const configContent = `import { defineConfig } from 'vitest/config';

export default defineConfig(${JSON.stringify(vitestConfig, null, 2)});
`;
    
    fs.writeFileSync(configPath, configContent);
    console.log(`   📝 Optimized Vitest config saved: ${configPath}`);
    
    this.metrics.optimizationsApplied.push('Vitest configuration optimized');
    return vitestConfig;
  }

  async detectFlakeyTests() {
    if (!this.options.enableFlakeDetection) return { flakeTests: [], analysis: {} };
    
    console.log('🔍 Detecting flakey tests...');
    
    const flakeAnalysis = {
      suspiciousTests: new Map(),
      patterns: new Map(),
      recommendations: []
    };

    try {
      // Analyze test history if available
      const testResultsPath = './reports/test-results.json';
      if (fs.existsSync(testResultsPath)) {
        const testResults = JSON.parse(fs.readFileSync(testResultsPath, 'utf8'));
        
        // Analyze test failures and patterns
        if (testResults.testResults) {
          for (const result of testResults.testResults) {
            if (result.status === 'failed') {
              const testName = result.name || result.title;
              if (testName) {
                if (!flakeAnalysis.suspiciousTests.has(testName)) {
                  flakeAnalysis.suspiciousTests.set(testName, []);
                }
                flakeAnalysis.suspiciousTests.get(testName).push({
                  timestamp: new Date().toISOString(),
                  error: result.failureMessage,
                  duration: result.duration
                });
              }
            }
          }
        }
      }

      // Pattern analysis
      for (const [testName, failures] of flakeAnalysis.suspiciousTests) {
        const failureRate = failures.length / 10; // Assuming last 10 runs
        if (failureRate >= this.config.flakeDetection.threshold) {
          this.metrics.flakeTests.add(testName);
          
          // Analyze failure patterns
          const errorTexts = failures.map(f => f.error || '').join(' ').toLowerCase();
          for (const [category, keywords] of Object.entries(this.config.flakeDetection.patterns)) {
            const matches = keywords.filter(keyword => errorTexts.includes(keyword));
            if (matches.length > 0) {
              if (!flakeAnalysis.patterns.has(category)) {
                flakeAnalysis.patterns.set(category, new Set());
              }
              matches.forEach(match => flakeAnalysis.patterns.get(category).add(match));
            }
          }
        }
      }

      // Generate recommendations
      if (flakeAnalysis.patterns.has('timeoutKeywords')) {
        flakeAnalysis.recommendations.push('Consider increasing test timeouts or investigating test performance');
      }
      if (flakeAnalysis.patterns.has('concurrencyKeywords')) {
        flakeAnalysis.recommendations.push('Review concurrent test execution and add proper synchronization');
      }
      if (flakeAnalysis.patterns.has('resourceKeywords')) {
        flakeAnalysis.recommendations.push('Investigate memory leaks and resource cleanup in tests');
      }

      console.log(`   🎯 Identified ${this.metrics.flakeTests.size} potentially flaky tests`);
      console.log(`   📋 Found ${flakeAnalysis.patterns.size} failure pattern categories`);

    } catch (error) {
      console.warn(`Warning: Could not analyze flaky tests: ${error.message}`);
    }

    return {
      flakeTests: Array.from(this.metrics.flakeTests),
      analysis: Object.fromEntries(flakeAnalysis.patterns),
      recommendations: flakeAnalysis.recommendations
    };
  }

  async optimizeTestPerformance() {
    if (!this.options.enablePerformanceOptimization) return null;
    
    console.log('🚀 Optimizing test performance...');
    
    const optimizations = {
      applied: [],
      recommendations: [],
      metrics: {}
    };

    try {
      // Memory optimization
      if (this.config.performance.optimization.enableResourceMonitoring) {
        process.on('beforeExit', () => {
          const memUsage = process.memoryUsage();
          this.metrics.memoryUsage.set('final', memUsage);
          
          if (memUsage.heapUsed > this.config.performance.memoryLeakThreshold) {
            optimizations.recommendations.push('Potential memory leak detected - review test cleanup');
          }
        });
        
        optimizations.applied.push('Memory monitoring enabled');
      }

      // Parallel test execution optimization
      if (this.config.performance.parallelization.enabled) {
        const packageJsonPath = './package.json';
        if (fs.existsSync(packageJsonPath)) {
          const packageJson = JSON.parse(fs.readFileSync(packageJsonPath, 'utf8'));
          
          // Add optimized test scripts if they don't exist
          const optimizedScripts = {
            'test:parallel': `vitest run --config vitest.optimized.config.ts --reporter=verbose`,
            'test:parallel:ci': `vitest run --config vitest.optimized.config.ts --reporter=junit --reporter=json`,
            'test:performance': `vitest run --config vitest.optimized.config.ts --reporter=verbose --run --coverage=false`,
            'test:flake-detection': `vitest run --config vitest.optimized.config.ts --retry=5 --reporter=json`
          };

          let scriptsAdded = false;
          for (const [scriptName, command] of Object.entries(optimizedScripts)) {
            if (!packageJson.scripts[scriptName]) {
              packageJson.scripts[scriptName] = command;
              scriptsAdded = true;
            }
          }

          if (scriptsAdded) {
            fs.writeFileSync(packageJsonPath, JSON.stringify(packageJson, null, 2));
            optimizations.applied.push('Optimized test scripts added to package.json');
          }
        }
      }

      console.log(`   ✅ Applied ${optimizations.applied.length} performance optimizations`);

    } catch (error) {
      console.warn(`Warning: Could not optimize performance: ${error.message}`);
    }

    return optimizations;
  }

  async generateComprehensiveReport() {
    if (!this.options.generateReports) return null;
    
    console.log('📊 Generating comprehensive optimization report...');
    
    const report = {
      timestamp: new Date().toISOString(),
      environment: {
        isCI: this.isCI,
        nodeVersion: process.version,
        platform: process.platform
      },
      metrics: {
        ...this.metrics,
        flakeTests: Array.from(this.metrics.flakeTests),
        performanceIssues: Object.fromEntries(this.metrics.performanceIssues),
        memoryUsage: Object.fromEntries(this.metrics.memoryUsage)
      },
      configuration: this.config,
      optimizations: this.metrics.optimizationsApplied,
      recommendations: [
        'Use npm run test:parallel:ci for CI environments',
        'Monitor flaky tests with npm run test:flake-detection',
        'Regular performance analysis with npm run test:performance',
        'Review memory usage patterns for leak detection',
        'Update timeout configurations based on CI performance'
      ],
      nextSteps: [
        'Monitor optimization effectiveness over next CI runs',
        'Adjust configuration based on performance metrics',
        'Implement automated flaky test isolation',
        'Set up performance regression alerts'
      ]
    };

    const reportPath = path.join(this.reportsDir, 'optimization-report.json');
    await fsp.writeFile(reportPath, JSON.stringify(report, null, 2));
    
    // Generate human-readable summary
    const summaryPath = path.join(this.reportsDir, 'optimization-summary.md');
    const summary = this.generateMarkdownSummary(report);
    await fsp.writeFile(summaryPath, summary);
    
    console.log(`   📄 Detailed report: ${reportPath}`);
    console.log(`   📋 Summary report: ${summaryPath}`);
    
    return report;
  }

  generateMarkdownSummary(report) {
    return `# CI/Test Optimization Report

Generated: ${report.timestamp}

## Environment
- CI Environment: ${report.environment.isCI ? 'Yes' : 'No'}
- Node Version: ${report.environment.nodeVersion}
- Platform: ${report.environment.platform}

## Optimizations Applied
${report.optimizations.map(opt => `- ✅ ${opt}`).join('\n')}

## Flaky Test Detection
- Potentially flaky tests detected: ${report.metrics.flakeTests.length}
${report.metrics.flakeTests.map(test => `  - ⚠️ ${test}`).join('\n')}

## Performance Metrics
- Memory usage monitored: ${Object.keys(report.metrics.memoryUsage).length > 0 ? 'Yes' : 'No'}
- Performance issues tracked: ${Object.keys(report.metrics.performanceIssues).length}

## Recommendations
${report.recommendations.map(rec => `- 💡 ${rec}`).join('\n')}

## Next Steps
${report.nextSteps.map(step => `- 🎯 ${step}`).join('\n')}

---
*Generated by Integrated CI/Test Optimizer*
`;
  }

  async displaySummary() {
    console.log('\n📋 CI/Test Optimization Summary:');
    console.log(`   🏗️ Environment: ${this.isCI ? 'CI' : 'Local'}`);
    console.log(`   ⚙️ Optimizations applied: ${this.metrics.optimizationsApplied.length}`);
    console.log(`   🎯 Flaky tests detected: ${this.metrics.flakeTests.size}`);
    console.log(`   📊 Configuration optimized: ${this.options.enableStabilityEnhancement ? 'Yes' : 'No'}`);
    console.log(`   🚀 Performance enhanced: ${this.options.enablePerformanceOptimization ? 'Yes' : 'No'}`);
    
    if (this.metrics.optimizationsApplied.length > 0) {
      console.log('\n✅ Applied Optimizations:');
      this.metrics.optimizationsApplied.forEach(opt => {
        console.log(`   • ${opt}`);
      });
    }
    
    if (this.metrics.flakeTests.size > 0) {
      console.log('\n⚠️ Potentially Flaky Tests:');
      Array.from(this.metrics.flakeTests).slice(0, 5).forEach(test => {
        console.log(`   • ${test}`);
      });
      if (this.metrics.flakeTests.size > 5) {
        console.log(`   • ... and ${this.metrics.flakeTests.size - 5} more`);
      }
    }
    
    console.log(`\n📁 Reports saved to: ${this.reportsDir}/`);
  }

  async run() {
    const startTime = Date.now();
    
    try {
      console.log('🚀 Starting integrated CI/Test optimization...\n');
      
      await this.ensureDirectories();
      
      const environmentAnalysis = await this.analyzeTestEnvironment();
      
      const vitestConfig = await this.optimizeVitestConfiguration();
      
      const flakeDetection = await this.detectFlakeyTests();
      
      const performanceOptimization = await this.optimizeTestPerformance();
      
      const report = await this.generateComprehensiveReport();
      
      this.metrics.executionTime = Date.now() - startTime;
      
      await this.displaySummary();
      
      console.log('\n✅ CI/Test optimization completed successfully!');
      console.log(`⏱️ Total execution time: ${this.metrics.executionTime}ms`);
      
      return {
        environmentAnalysis,
        vitestConfig,
        flakeDetection,
        performanceOptimization,
        report,
        metrics: this.metrics
      };
      
    } catch (error) {
      console.error(`❌ Optimization failed: ${error.message}`);
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
      case '--no-flake-detection':
        options.enableFlakeDetection = false;
        break;
      case '--no-stability':
        options.enableStabilityEnhancement = false;
        break;
      case '--no-performance':
        options.enablePerformanceOptimization = false;
        break;
      case '--no-reports':
        options.generateReports = false;
        break;
      case '--ci':
        process.env.CI = 'true';
        break;
      case '--help':
        console.log(`
Integrated CI/Test Optimizer

Usage: node integrated-ci-test-optimizer.mjs [options]

Options:
  --no-flake-detection    Disable flaky test detection
  --no-stability          Disable stability enhancements
  --no-performance        Disable performance optimizations
  --no-reports            Disable report generation
  --ci                    Force CI mode
  --help                  Show this help message
        `);
        process.exit(0);
    }
  }
  
  const optimizer = new IntegratedCITestOptimizer(options);
  await optimizer.run();
}

if (import.meta.url === pathToFileURL(process.argv[1]).href) {
  main().catch(error => {
    console.error('💥 Failed:', error.message);
    process.exit(1);
  });
}

export { IntegratedCITestOptimizer };