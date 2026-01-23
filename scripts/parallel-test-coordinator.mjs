#!/usr/bin/env node

/**
 * Parallel Test Execution Coordinator
 * Manages intelligent test distribution and resource allocation
 */

import { spawn } from 'child_process';
import { promises as fs } from 'fs';
import { cpus } from 'os';
import path from 'path';

class ParallelTestCoordinator {
  constructor() {
    const envMax = Number.parseInt(process.env.MAX_TEST_CONCURRENCY ?? '', 10);
    const defaultMax = Math.min(cpus().length, 4); // Limit to prevent resource exhaustion
    this.maxConcurrency = Number.isFinite(envMax) && envMax > 0 ? envMax : defaultMax;
    const envMultiplier = Number.parseFloat(process.env.RESOURCE_WEIGHT_MULTIPLIER ?? '1');
    this.resourceWeightMultiplier = Number.isFinite(envMultiplier) && envMultiplier > 0 ? envMultiplier : 1;
    this.useContainerTests = process.env.AE_PARALLEL_USE_CONTAINER === '1';
    this.activeJobs = new Map();
    this.completedJobs = new Map();
    this.failedJobs = new Map();
    const allSuites = [
      {
        name: 'unit',
        command: ['pnpm', 'run', 'test:unit'],
        containerCommand: ['bash', 'scripts/docker/run-unit.sh'],
        priority: 1,
        estimatedDuration: 300000, // 5 minutes
        resourceWeight: 1,
        dependencies: []
      },
      {
        name: 'integration',
        command: ['pnpm', 'run', 'test:int'],
        priority: 2,
        estimatedDuration: 600000, // 10 minutes
        resourceWeight: 2,
        dependencies: ['unit']
      },
      {
        name: 'quality',
        command: ['pnpm', 'run', 'test:quality:fast'],
        priority: 2,
        estimatedDuration: 900000, // 15 minutes
        resourceWeight: 2,
        dependencies: []
      },
      {
        name: 'e2e',
        command: ['pnpm', 'run', 'test:e2e'],
        priority: 3,
        estimatedDuration: 1200000, // 20 minutes
        resourceWeight: 3,
        dependencies: ['unit', 'integration']
      },
      {
        name: 'flake-detection',
        command: ['pnpm', 'run', 'test:flake-detection'],
        priority: 4,
        estimatedDuration: 800000, // 13 minutes
        resourceWeight: 2,
        dependencies: []
      }
    ];

    // Optional suite selection for partial runs (useful for CI/triage).
    // NOTE: Dependencies are validated to prevent deadlocks (e.g. running "integration" without "unit").
    const parseSuiteList = (value) =>
      String(value ?? '')
        .split(',')
        .map((item) => item.trim())
        .filter(Boolean);

    const includeRaw = parseSuiteList(process.env.AE_PARALLEL_SUITES);
    const excludeRaw = parseSuiteList(process.env.AE_PARALLEL_EXCLUDE_SUITES);

    const suiteByName = new Map(allSuites.map((suite) => [suite.name, suite]));
    const knownNames = new Set(suiteByName.keys());

    const assertKnown = (names, label) => {
      const unknown = names.filter((name) => !knownNames.has(name));
      if (unknown.length > 0) {
        throw new Error(`[parallel] unknown ${label} suite(s): ${unknown.join(', ')}`);
      }
    };

    assertKnown(includeRaw, 'include');
    assertKnown(excludeRaw, 'exclude');

    const exclude = new Set(excludeRaw);

    const selectWithDependencies = (names) => {
      const selected = new Set();
      const stack = [...new Set(names)];
      while (stack.length > 0) {
        const name = stack.pop();
        if (!name || selected.has(name)) continue;
        const suite = suiteByName.get(name);
        if (!suite) continue;
        selected.add(name);
        for (const dep of suite.dependencies ?? []) {
          if (!selected.has(dep)) stack.push(dep);
        }
      }
      return selected;
    };

    let selectedNames = includeRaw.length > 0
      ? selectWithDependencies(includeRaw)
      : new Set(knownNames);

    for (const name of exclude) {
      selectedNames.delete(name);
    }

    // Validate dependencies for the final selection.
    for (const name of selectedNames) {
      const suite = suiteByName.get(name);
      for (const dep of suite?.dependencies ?? []) {
        if (!selectedNames.has(dep)) {
          throw new Error(`[parallel] suite "${name}" requires "${dep}" (excluded or not selected)`);
        }
      }
    }

    this.testSuites = Array.from(selectedNames).map((name) => suiteByName.get(name));
  }

  async execute() {
    console.log('🚀 Starting parallel test execution coordinator...');
    console.log(`📊 Available CPU cores: ${cpus().length}, Max concurrency: ${this.maxConcurrency}`);

    const startTime = Date.now();
    await this.createReportsDirectory();

    try {
      await this.executeTestSuites();
      await this.generateExecutionReport(startTime);

      if (this.failedJobs.size > 0) {
        console.log(`❌ ${this.failedJobs.size} test suite(s) failed`);
        process.exit(1);
      } else {
        console.log('✅ All test suites completed successfully');
        process.exit(0);
      }
    } catch (error) {
      console.error('💥 Coordinator execution failed:', error.message);
      process.exit(1);
    }
  }

  async createReportsDirectory() {
    const dirs = ['reports', 'logs', 'reports/parallel-execution'];
    for (const dir of dirs) {
      await fs.mkdir(dir, { recursive: true });
    }
  }

  async executeTestSuites() {
    const executionQueue = [...this.testSuites].sort((a, b) => a.priority - b.priority);

    while (executionQueue.length > 0 || this.activeJobs.size > 0) {
      // Start new jobs if resources allow
      while (this.canStartNewJob() && executionQueue.length > 0) {
        const nextSuite = this.findNextExecutableJob(executionQueue);
        if (nextSuite) {
          const index = executionQueue.indexOf(nextSuite);
          executionQueue.splice(index, 1);
          await this.startTestJob(nextSuite);
        } else {
          break; // No executable jobs available, wait for dependencies
        }
      }

      // Wait for any job to complete
      if (this.activeJobs.size > 0) {
        await this.waitForNextCompletion();
      }
    }
  }

  canStartNewJob() {
    const currentResourceLoad = Array.from(this.activeJobs.values())
      .reduce((sum, job) => sum + this.getResourceWeight(job.suite), 0);

    return this.activeJobs.size < this.maxConcurrency && currentResourceLoad < this.maxConcurrency * 2;
  }

  findNextExecutableJob(queue) {
    return queue.find(suite => this.areDependenciesSatisfied(suite));
  }

  areDependenciesSatisfied(suite) {
    return suite.dependencies.every(dep => this.completedJobs.has(dep));
  }

  async startTestJob(suite) {
    const { cmd, args, mode } = await this.resolveCommand(suite);
    console.log(`🏃 Starting ${suite.name} test suite (mode: ${mode}, priority: ${suite.priority}, weight: ${this.getResourceWeight(suite)})`);

    const startTime = Date.now();
    const logFile = path.join('logs', `parallel-${suite.name}-${Date.now()}.log`);

    const jobPromise = new Promise((resolve, reject) => {
      // Avoid shadowing global `process` (Node.js). Use `child` for the spawned process.
      const child = spawn(cmd, args, {
        stdio: 'pipe',
        // Use the real Node.js process.env explicitly to prevent CodeQL issue (property access on non-object)
        env: { ...process.env, TEST_SUITE: suite.name }
      });

      let stdout = '';
      let stderr = '';

      child.stdout?.on('data', (data) => {
        stdout += data.toString();
      });

      child.stderr?.on('data', (data) => {
        stderr += data.toString();
      });

      child.on('close', async (code) => {
        const endTime = Date.now();
        const duration = endTime - startTime;

        const result = {
          suite,
          code,
          duration,
          stdout,
          stderr,
          startTime,
          endTime,
          command: [cmd, ...args].join(' '),
          mode
        };

        // Save execution log
        await this.saveExecutionLog(logFile, result);

        if (code === 0) {
          console.log(`✅ ${suite.name} completed successfully in ${(duration / 1000).toFixed(1)}s`);
          this.completedJobs.set(suite.name, result);
          resolve(result);
        } else {
          console.log(`❌ ${suite.name} failed with code ${code} after ${(duration / 1000).toFixed(1)}s`);
          this.failedJobs.set(suite.name, result);
          reject(new Error(`Test suite ${suite.name} failed`));
        }
      });

      child.on('error', (error) => {
        console.error(`💥 Process error for ${suite.name}:`, error.message);
        reject(error);
      });
    });

    this.activeJobs.set(suite.name, { suite, promise: jobPromise, startTime });

    return jobPromise;
  }

  async waitForNextCompletion() {
    const activePromises = Array.from(this.activeJobs.values()).map(job =>
      job.promise.catch(() => {}) // Ignore rejections here, handle in job completion
    );

    await Promise.race(activePromises);

    // Clean up completed jobs from active list
    for (const name of this.activeJobs.keys()) {
      if (this.completedJobs.has(name) || this.failedJobs.has(name)) {
        this.activeJobs.delete(name);
      }
    }
  }

  async saveExecutionLog(logFile, result) {
    const log = {
      timestamp: new Date().toISOString(),
      suite: result.suite.name,
      exitCode: result.code,
      mode: result.mode,
      command: result.command,
      duration: result.duration,
      estimatedDuration: result.suite.estimatedDuration,
      variance: result.duration - result.suite.estimatedDuration,
      stdout: result.stdout.substring(0, 5000), // Truncate for storage
      stderr: result.stderr.substring(0, 5000)
    };

    await fs.writeFile(logFile, JSON.stringify(log, null, 2));
  }

  async generateExecutionReport(startTime) {
    const totalDuration = Date.now() - startTime;
    const allJobs = new Map([...this.completedJobs, ...this.failedJobs]);

    const report = {
      timestamp: new Date().toISOString(),
      totalDuration,
      maxConcurrency: this.maxConcurrency,
      resourceWeightMultiplier: this.resourceWeightMultiplier,
      summary: {
        total: allJobs.size,
        completed: this.completedJobs.size,
        failed: this.failedJobs.size,
        successRate: (this.completedJobs.size / allJobs.size * 100).toFixed(2) + '%'
      },
      performance: {
        totalExecutionTime: Array.from(allJobs.values())
          .reduce((sum, job) => sum + job.duration, 0),
        parallelEfficiency: this.calculateParallelEfficiency(allJobs, totalDuration),
        averageJobDuration: Array.from(allJobs.values())
          .reduce((sum, job) => sum + job.duration, 0) / allJobs.size
      },
      jobs: Object.fromEntries(
        Array.from(allJobs.entries()).map(([name, job]) => [
          name,
          {
            status: this.completedJobs.has(name) ? 'completed' : 'failed',
            duration: job.duration,
            estimatedDuration: job.suite.estimatedDuration,
            variance: job.duration - job.suite.estimatedDuration,
            resourceWeight: job.suite.resourceWeight,
            effectiveResourceWeight: this.getResourceWeight(job.suite),
            priority: job.suite.priority
          }
        ])
      ),
      resourceUtilization: this.calculateResourceUtilization(allJobs),
      recommendations: this.generateOptimizationRecommendations(allJobs, totalDuration)
    };

    const reportPath = path.join('reports', 'parallel-execution', `execution-report-${Date.now()}.json`);
    await fs.writeFile(reportPath, JSON.stringify(report, null, 2));

    console.log(`📊 Execution report saved: ${reportPath}`);
    console.log(`⏱️  Total execution time: ${(totalDuration / 1000).toFixed(1)}s`);
    console.log(`🎯 Parallel efficiency: ${report.performance.parallelEfficiency.toFixed(1)}%`);

    return report;
  }

  calculateParallelEfficiency(allJobs, totalDuration) {
    const sequentialTime = Array.from(allJobs.values())
      .reduce((sum, job) => sum + job.duration, 0);

    return (sequentialTime / totalDuration) * 100;
  }

  calculateResourceUtilization(allJobs) {
    const jobsByWeight = Array.from(allJobs.values())
      .reduce((acc, job) => {
        const weight = this.getResourceWeight(job.suite);
        acc[weight] = (acc[weight] || 0) + 1;
        return acc;
      }, {});

    return {
      distributionByWeight: jobsByWeight,
      averageWeight: Array.from(allJobs.values())
        .reduce((sum, job) => sum + this.getResourceWeight(job.suite), 0) / allJobs.size
    };
  }

  generateOptimizationRecommendations(allJobs, totalDuration) {
    const recommendations = [];

    // Analyze duration variances
    const highVarianceJobs = Array.from(allJobs.values())
      .filter(job => Math.abs(job.duration - job.suite.estimatedDuration) > 60000)
      .map(job => job.suite.name);

    if (highVarianceJobs.length > 0) {
      recommendations.push({
        type: 'duration_estimation',
        message: `Update duration estimates for: ${highVarianceJobs.join(', ')}`,
        impact: 'medium'
      });
    }

    // Analyze parallel efficiency
    const efficiency = this.calculateParallelEfficiency(allJobs, totalDuration);
    if (efficiency < 70) {
      recommendations.push({
        type: 'concurrency',
        message: 'Consider increasing max concurrency or optimizing resource weights',
        impact: 'high'
      });
    }

    // Analyze failed jobs
    if (this.failedJobs.size > 0) {
      recommendations.push({
        type: 'reliability',
        message: `Investigate and fix failing test suites: ${Array.from(this.failedJobs.keys()).join(', ')}`,
        impact: 'high'
      });
    }

    return recommendations;
  }

  getResourceWeight(suite) {
    return suite.resourceWeight * this.resourceWeightMultiplier;
  }

  async resolveCommand(suite) {
    if (this.useContainerTests && suite.containerCommand) {
      const [cmd, ...args] = suite.containerCommand;
      if (await this.isCommandRunnable(cmd, args)) {
        return { cmd, args, mode: 'container' };
      }
      console.warn(`[parallel] container command unavailable for ${suite.name}; falling back to host`);
    }
    const [cmd, ...args] = suite.command;
    return { cmd, args, mode: 'host' };
  }

  async isCommandRunnable(cmd, args) {
    if (cmd === 'bash' && args.length > 0) {
      const target = path.resolve(process.cwd(), args[0]);
      try {
        await fs.access(target);
        return true;
      } catch {
        return false;
      }
    }
    return true;
  }
}

// CLI execution
async function main() {
  const coordinator = new ParallelTestCoordinator();
  await coordinator.execute();
}

if (import.meta.url === `file://${process.argv[1]}`) {
  main().catch(error => {
    console.error('💥 Coordinator failed:', error.message);
    process.exit(1);
  });
}

export { ParallelTestCoordinator };
