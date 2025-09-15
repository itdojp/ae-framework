#!/usr/bin/env node

/**
 * Req2Run Benchmark CLI
 * Command-line interface for running AE Framework benchmarks
 */

import { Command } from 'commander';
import chalk from 'chalk';
import { toMessage } from '../utils/error-utils.js';
import { BenchmarkRunner } from '../benchmark/req2run/runners/BenchmarkRunner.js';
import { 
  DEFAULT_BENCHMARK_CONFIG, 
  getConfigForDifficulty, 
  getConfigForCategory,
  getCIConfig 
} from '../benchmark/req2run/config/default.js';
import type { 
  BenchmarkConfig, 
  BenchmarkResult 
} from '../benchmark/req2run/types/index.js';
import { DifficultyLevel, BenchmarkCategory } from '../benchmark/req2run/types/index.js';
import * as fs from 'fs/promises';
import * as path from 'path';
import { safeExit } from '../utils/safe-exit.js';

const program = new Command();

program
  .name('ae-benchmark')
  .description('Run AE Framework benchmarks against Req2Run problems')
  .version('1.0.0');

/**
 * Run benchmark command
 */
program
  .command('run')
  .description('Run benchmark problems')
  .option('-c, --config <path>', 'Configuration file path')
  .option('-p, --problems <ids...>', 'Specific problem IDs to run')
  .option('-d, --difficulty <level>', 'Difficulty level (basic|intermediate|advanced|expert)')
  .option('--category <category>', 'Problem category filter')
  .option('--parallel', 'Enable parallel execution')
  .option('--timeout <ms>', 'Execution timeout in milliseconds')
  .option('--output <path>', 'Output directory for results')
  .option('--ci', 'Use CI-optimized configuration')
  .option('--dry-run', 'Show what would be executed without running')
  .action(async (options) => {
    try {
      console.log('🏆 Starting AE Framework Benchmark Execution');
      console.log('==========================================');
      
      // Load configuration
      const config = await loadConfiguration(options);
      console.log(`📋 Configuration loaded: ${config.problems.length} problems enabled`);
      
      // Initialize benchmark runner
      const runner = new BenchmarkRunner(config);
      
      // Determine problems to run
      const problemIds = options.problems || 
        config.problems.filter(p => p.enabled).map(p => p.id);
      
      if (options.dryRun) {
        console.log('\n🔍 Dry Run - Problems that would be executed:');
        problemIds.forEach((id: string, index: number) => {
          const problem = config.problems.find(p => p.id === id);
          console.log(`  ${index + 1}. ${id} (${problem?.category}, ${problem?.difficulty})`);
        });
        return;
      }
      
      console.log(`\n🚀 Executing ${problemIds.length} benchmark problems...`);
      
      // Run benchmarks
      const startTime = Date.now();
      const results = await runner.runBenchmarks(problemIds);
      const endTime = Date.now();
      
      // Display results summary
      await displayResults(results, endTime - startTime);
      
      // Save results
      if (options.output) {
        await saveResults(results, options.output);
        console.log(`\n💾 Results saved to ${options.output}`);
      }
      
      // Exit with appropriate code
      const failedCount = results.filter(r => !r.success).length;
      safeExit(failedCount > 0 ? 1 : 0);
      
    } catch (error: unknown) {
      console.error(chalk.red(`❌ Benchmark execution failed: ${toMessage(error)}`));
      safeExit(1);
    }
  });

/**
 * List available problems command
 */
program
  .command('list')
  .description('List available benchmark problems')
  .option('-d, --difficulty <level>', 'Filter by difficulty level')
  .option('--category <category>', 'Filter by category')
  .option('--enabled-only', 'Show only enabled problems')
  .action(async (options) => {
    try {
      const config = DEFAULT_BENCHMARK_CONFIG;
      let problems = config.problems;
      
      // Apply filters
      if (options.difficulty) {
        const difficulty = options.difficulty as DifficultyLevel;
        problems = problems.filter(p => p.difficulty === difficulty);
      }
      
      if (options.category) {
        const category = options.category as BenchmarkCategory;
        problems = problems.filter(p => p.category === category);
      }
      
      if (options.enabledOnly) {
        problems = problems.filter(p => p.enabled);
      }
      
      console.log(`\n📋 Available Benchmark Problems (${problems.length} total)`);
      console.log('===========================================');
      
      // Group by category
      const groupedProblems = problems.reduce((groups, problem) => {
        if (!groups[problem.category]) {
          groups[problem.category] = [];
        }
        groups[problem?.category]?.push(problem);
        return groups;
      }, {} as Record<string, typeof problems>);
      
      for (const [category, categoryProblems] of Object.entries(groupedProblems)) {
        console.log(`\n📂 ${category.toUpperCase()}`);
        categoryProblems.forEach(problem => {
          const status = problem.enabled ? '✅' : '❌';
          const timeout = `${problem.timeoutMs / 1000}s`;
          console.log(`  ${status} ${problem.id} (${problem.difficulty}, timeout: ${timeout})`);
        });
      }
      
    } catch (error: unknown) {
      console.error(chalk.red(`❌ Failed to list problems: ${toMessage(error)}`));
      safeExit(1);
    }
  });

/**
 * Validate configuration command
 */
program
  .command('validate')
  .description('Validate benchmark configuration')
  .option('-c, --config <path>', 'Configuration file path')
  .action(async (options) => {
    try {
      const config = await loadConfiguration(options);
      
      console.log('✅ Configuration validation completed');
      console.log(`   - Problems: ${config.problems.length}`);
      console.log(`   - Enabled: ${config.problems.filter(p => p.enabled).length}`);
      console.log(`   - Parallel: ${config.execution.parallel}`);
      console.log(`   - Max Concurrency: ${config.execution.maxConcurrency}`);
      console.log(`   - Docker: ${config.execution.docker.enabled ? 'Enabled' : 'Disabled'}`);
      
    } catch (error: unknown) {
      console.error(chalk.red(`❌ Configuration validation failed: ${toMessage(error)}`));
      safeExit(1);
    }
  });

/**
 * Generate sample configuration command
 */
program
  .command('init')
  .description('Generate sample configuration file')
  .option('-o, --output <path>', 'Output file path', './benchmark-config.json')
  .option('--difficulty <level>', 'Template for specific difficulty')
  .option('--ci', 'Generate CI-optimized configuration')
  .action(async (options) => {
    try {
      let config: BenchmarkConfig;
      
      if (options.ci) {
        config = getCIConfig();
      } else if (options.difficulty) {
        const difficultyConfig = getConfigForDifficulty(options.difficulty as DifficultyLevel);
        config = { ...DEFAULT_BENCHMARK_CONFIG, ...difficultyConfig };
      } else {
        config = DEFAULT_BENCHMARK_CONFIG;
      }
      
      await fs.writeFile(options.output, JSON.stringify(config, null, 2));
      console.log(`✅ Configuration template saved to ${options.output}`);
      
    } catch (error: unknown) {
      console.error(chalk.red(`❌ Failed to generate configuration: ${toMessage(error)}`));
      process.exit(1);
    }
  });

/**
 * Load configuration from file or use defaults
 */
async function loadConfiguration(options: any): Promise<BenchmarkConfig> {
  let config = DEFAULT_BENCHMARK_CONFIG;
  
  // Load from file if specified
  if (options.config) {
    try {
      const configData = await fs.readFile(options.config, 'utf-8');
      const fileConfig = JSON.parse(configData);
      config = { ...config, ...fileConfig };
    } catch (error: unknown) {
      throw new Error(`Failed to load configuration from ${options.config}: ${toMessage(error)}`);
    }
  }
  
  // Apply command-line overrides
  if (options.ci) {
    config = getCIConfig();
  }
  
  if (options.difficulty) {
    const difficultyConfig = getConfigForDifficulty(options.difficulty as DifficultyLevel);
    config = { ...config, ...difficultyConfig };
  }
  
  if (options.category) {
    const categoryConfig = getConfigForCategory(options.category as BenchmarkCategory);
    config = { ...config, ...categoryConfig };
  }
  
  if (options.parallel !== undefined) {
    config.execution.parallel = options.parallel;
  }
  
  if (options.timeout) {
    const timeoutMs = parseInt(options.timeout);
    config.problems = config.problems.map(p => ({ ...p, timeoutMs }));
  }
  
  return config;
}

/**
 * Display benchmark results summary
 */
async function displayResults(results: BenchmarkResult[], totalTime: number): Promise<void> {
  const successCount = results.filter(r => r.success).length;
  const failureCount = results.length - successCount;
  const averageScore = results.reduce((sum, r) => sum + r.metrics.overallScore, 0) / results.length;
  
  console.log('\n📊 Benchmark Results Summary');
  console.log('============================');
  console.log(`⏱️  Total Time: ${(totalTime / 1000).toFixed(2)}s`);
  console.log(`✅ Successful: ${successCount}/${results.length}`);
  console.log(`❌ Failed: ${failureCount}/${results.length}`);
  console.log(`📈 Average Score: ${averageScore.toFixed(1)}/100`);
  
  if (results.length > 0) {
    console.log('\n📋 Individual Results:');
    results.forEach((result, index) => {
      const status = result.success ? '✅' : '❌';
      const score = result.metrics.overallScore.toFixed(1);
      const time = (result.executionDetails.totalDuration / 1000).toFixed(2);
      console.log(`  ${index + 1}. ${status} ${result.problemId} - Score: ${score}/100, Time: ${time}s`);
      
      if (!result.success && result.errors) {
        result.errors.forEach(error => {
          console.log(`     💥 ${error.phase}: ${error.message}`);
        });
      }
    });
  }
  
  // Show top performers
  const topResults = results
    .filter(r => r.success)
    .sort((a, b) => b.metrics.overallScore - a.metrics.overallScore)
    .slice(0, 3);
    
  if (topResults.length > 0) {
    console.log('\n🏆 Top Performers:');
    topResults.forEach((result, index) => {
      console.log(`  ${index + 1}. ${result.problemId} - ${result.metrics.overallScore.toFixed(1)}/100`);
    });
  }
}

/**
 * Save results to file
 */
async function saveResults(results: BenchmarkResult[], outputPath: string): Promise<void> {
  // Ensure output directory exists
  await fs.mkdir(path.dirname(outputPath), { recursive: true });
  
  const timestamp = new Date().toISOString().replace(/[:.]/g, '-');
  const jsonPath = path.join(outputPath, `benchmark-results-${timestamp}.json`);
  
  await fs.writeFile(jsonPath, JSON.stringify(results, null, 2));
}

// Handle unhandled promise rejections
process.on('unhandledRejection', (reason, promise) => {
  console.error(chalk.red('❌ Unhandled Rejection at:'), promise, 'reason:', reason);
  safeExit(1);
});

// Execute the CLI
program.parse();
