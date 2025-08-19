#!/usr/bin/env node

import { Command } from 'commander';
import chalk from 'chalk';
import {
  ResilienceSystem,
  createResilienceSystem,
  CircuitState,
  type ResilienceConfig,
} from '../resilience/index.js';

/**
 * Resilience System CLI
 * Provides command-line interface for resilience pattern management and monitoring
 */
export class ResilienceCLI {
  private systems: Map<string, ResilienceSystem> = new Map();

  constructor() {
    // Create default system
    this.systems.set('default', createResilienceSystem('default'));
  }

  /**
   * Create a resilience system with configuration
   */
  async createSystem(options: {
    name: string;
    preset?: 'default' | 'aggressive' | 'conservative' | 'minimal';
    config?: string; // JSON config file path
  }): Promise<void> {
    try {
      let system: ResilienceSystem;

      if (options.config) {
        // Load config from file
        const fs = await import('fs');
        const configData = JSON.parse(fs.readFileSync(options.config, 'utf8'));
        system = new ResilienceSystem(configData);
      } else {
        system = createResilienceSystem(options.preset || 'default');
      }

      this.systems.set(options.name, system);

      console.log(chalk.green(`✅ Resilience system '${options.name}' created successfully`));
      console.log(chalk.blue(`   Preset: ${options.preset || 'custom'}`));
      
      const config = system.getConfig();
      console.log(chalk.blue(`   Retry enabled: ${config.retry?.enabled}`));
      console.log(chalk.blue(`   Circuit breaker enabled: ${config.circuitBreaker?.enabled}`));
      console.log(chalk.blue(`   Rate limiter enabled: ${config.rateLimiter?.enabled}`));
      console.log(chalk.blue(`   Bulkhead enabled: ${config.bulkhead?.enabled}`));
      console.log(chalk.blue(`   Timeout enabled: ${config.timeout?.enabled}`));
      
    } catch (error) {
      console.error(chalk.red(`❌ Failed to create resilience system: ${error}`));
      process.exit(1);
    }
  }

  /**
   * List all resilience systems
   */
  async listSystems(): Promise<void> {
    if (this.systems.size === 0) {
      console.log(chalk.yellow('No resilience systems found'));
      return;
    }

    console.log(chalk.blue(`📋 Resilience Systems (${this.systems.size})`));
    console.log();

    for (const [name, system] of this.systems) {
      const health = system.getSystemHealth();
      const config = system.getConfig();
      
      const healthIcon = health.overall ? '✅' : '❌';
      const healthColor = health.overall ? chalk.green : chalk.red;
      
      console.log(healthColor(`${healthIcon} ${name}`));
      console.log(chalk.gray(`   Overall Health: ${health.overall ? 'Healthy' : 'Unhealthy'}`));
      
      if (health.components.circuitBreaker) {
        console.log(chalk.gray(`   Circuit Breaker: ${health.components.circuitBreaker.state}`));
      }
      
      if (health.components.rateLimiter) {
        console.log(chalk.gray(`   Rate Limiter: ${health.components.rateLimiter.availableTokens}/${health.components.rateLimiter.maxTokens} tokens`));
      }
      
      console.log(chalk.gray(`   Bulkheads: ${health.bulkheadSystem.healthyBulkheads}/${health.bulkheadSystem.totalBulkheads} healthy`));
      console.log();
    }
  }

  /**
   * Get detailed health statistics
   */
  async getHealth(systemName: string = 'default'): Promise<void> {
    const system = this.systems.get(systemName);
    if (!system) {
      console.error(chalk.red(`❌ Resilience system '${systemName}' not found`));
      process.exit(1);
    }

    const health = system.getSystemHealth();
    
    console.log(chalk.blue(`🏥 Health Report for '${systemName}'`));
    console.log();
    
    const overallIcon = health.overall ? '✅' : '❌';
    const overallColor = health.overall ? chalk.green : chalk.red;
    console.log(overallColor(`${overallIcon} Overall Health: ${health.overall ? 'Healthy' : 'Unhealthy'}`));
    console.log();

    // Circuit Breaker Health
    if (health.components.circuitBreaker) {
      const cb = health.components.circuitBreaker;
      const stateColor = cb.state === CircuitState.CLOSED ? chalk.green : 
                        cb.state === CircuitState.HALF_OPEN ? chalk.yellow : chalk.red;
      
      console.log(chalk.blue('🔌 Circuit Breaker'));
      console.log(stateColor(`   State: ${cb.state}`));
      console.log(chalk.gray(`   Failures: ${cb.failures}`));
      console.log(chalk.gray(`   Successes: ${cb.successes}`));
      console.log(chalk.gray(`   Total Requests: ${cb.totalRequests}`));
      console.log();
    }

    // Rate Limiter Health
    if (health.components.rateLimiter) {
      const rl = health.components.rateLimiter;
      const utilizationPercent = ((rl.maxTokens - rl.availableTokens) / rl.maxTokens * 100).toFixed(1);
      
      console.log(chalk.blue('🚦 Rate Limiter'));
      console.log(chalk.gray(`   Available Tokens: ${rl.availableTokens}/${rl.maxTokens}`));
      console.log(chalk.gray(`   Utilization: ${utilizationPercent}%`));
      console.log();
    }

    // Bulkhead Health
    const bulkheadHealth = health.bulkheadSystem;
    console.log(chalk.blue('🏗️ Bulkhead System'));
    console.log(chalk.gray(`   Total Bulkheads: ${bulkheadHealth.totalBulkheads}`));
    console.log(chalk.gray(`   Healthy Bulkheads: ${bulkheadHealth.healthyBulkheads}`));
    console.log(chalk.gray(`   Total Active: ${bulkheadHealth.totalActive}`));
    console.log(chalk.gray(`   Total Queued: ${bulkheadHealth.totalQueued}`));
    console.log(chalk.gray(`   Average Load: ${(bulkheadHealth.averageLoadFactor * 100).toFixed(1)}%`));

    if (Object.keys(health.components.bulkheads).length > 0) {
      console.log(chalk.blue('   Individual Bulkheads:'));
      for (const [name, stats] of Object.entries(health.components.bulkheads)) {
        const healthIcon = stats.active < stats.maxConcurrent ? '✅' : '⚠️';
        console.log(chalk.gray(`     ${healthIcon} ${name}: ${stats.active}/${stats.maxConcurrent} active, ${stats.queued}/${stats.maxQueued} queued`));
      }
    }
    console.log();

    // Timeout Health
    if (Object.keys(health.components.timeouts).length > 0) {
      console.log(chalk.blue('⏱️ Timeout Managers'));
      for (const [name, stats] of Object.entries(health.components.timeouts)) {
        const timeoutRate = (stats.timeoutRate * 100).toFixed(1);
        console.log(chalk.gray(`   ${name}: ${stats.totalOperations} ops, ${timeoutRate}% timeout rate`));
        console.log(chalk.gray(`     Current timeout: ${stats.currentTimeoutMs}ms`));
        console.log(chalk.gray(`     Average execution: ${stats.averageExecutionTime.toFixed(1)}ms`));
      }
      console.log();
    }
  }

  /**
   * Reset resilience system statistics
   */
  async resetSystem(systemName: string = 'default'): Promise<void> {
    const system = this.systems.get(systemName);
    if (!system) {
      console.error(chalk.red(`❌ Resilience system '${systemName}' not found`));
      process.exit(1);
    }

    system.reset();
    console.log(chalk.green(`✅ Resilience system '${systemName}' reset successfully`));
  }

  /**
   * Test resilience system with simulated operations
   */
  async testSystem(options: {
    systemName?: string;
    operations?: number;
    failureRate?: number;
    bulkheadName?: string;
  }): Promise<void> {
    const systemName = options.systemName || 'default';
    const system = this.systems.get(systemName);
    if (!system) {
      console.error(chalk.red(`❌ Resilience system '${systemName}' not found`));
      process.exit(1);
    }

    const operations = options.operations || 10;
    const failureRate = options.failureRate || 0.2;
    
    console.log(chalk.blue(`🧪 Testing resilience system '${systemName}'`));
    console.log(chalk.gray(`   Operations: ${operations}`));
    console.log(chalk.gray(`   Failure rate: ${(failureRate * 100).toFixed(1)}%`));
    console.log();

    let successes = 0;
    let failures = 0;

    for (let i = 0; i < operations; i++) {
      try {
        await system.executeResilient(
          async () => {
            // Simulate operation with potential failure
            if (Math.random() < failureRate) {
              throw new Error(`Simulated failure ${i + 1}`);
            }
            await new Promise(resolve => setTimeout(resolve, Math.random() * 100));
            return `Operation ${i + 1} success`;
          },
          {
            operationName: `test-op-${i + 1}`,
            bulkheadName: options.bulkheadName,
            timeoutMs: 5000,
            useAdaptiveTimeout: true,
          }
        );
        successes++;
        process.stdout.write(chalk.green('.'));
      } catch (error) {
        failures++;
        process.stdout.write(chalk.red('x'));
      }
    }

    console.log('\n');
    console.log(chalk.green(`✅ Successes: ${successes}`));
    console.log(chalk.red(`❌ Failures: ${failures}`));
    console.log(chalk.blue(`📊 Success rate: ${((successes / operations) * 100).toFixed(1)}%`));
    console.log();

    // Show health after test
    await this.getHealth(systemName);
  }

  /**
   * Export system configuration
   */
  async exportConfig(systemName: string = 'default', outputPath?: string): Promise<void> {
    const system = this.systems.get(systemName);
    if (!system) {
      console.error(chalk.red(`❌ Resilience system '${systemName}' not found`));
      process.exit(1);
    }

    const config = system.getConfig();
    const configJson = JSON.stringify(config, null, 2);

    if (outputPath) {
      const fs = await import('fs');
      fs.writeFileSync(outputPath, configJson);
      console.log(chalk.green(`✅ Configuration exported to ${outputPath}`));
    } else {
      console.log(chalk.blue('📄 System Configuration:'));
      console.log(configJson);
    }
  }
}

/**
 * Create resilience command for CLI
 */
export function createResilienceCommand(): Command {
  const command = new Command('resilience');
  command.description('Resilience system management and monitoring');
  
  const cli = new ResilienceCLI();

  command
    .command('create')
    .description('Create a new resilience system')
    .option('-n, --name <name>', 'System name', 'default')
    .option('-p, --preset <preset>', 'Configuration preset (default|aggressive|conservative|minimal)', 'default')
    .option('-c, --config <path>', 'Configuration file path')
    .action(async (options) => {
      await cli.createSystem(options);
    });

  command
    .command('list')
    .description('List all resilience systems')
    .action(async () => {
      await cli.listSystems();
    });

  command
    .command('health')
    .description('Get health statistics for a resilience system')
    .option('-n, --name <name>', 'System name', 'default')
    .action(async (options) => {
      await cli.getHealth(options.name);
    });

  command
    .command('reset')
    .description('Reset resilience system statistics')
    .option('-n, --name <name>', 'System name', 'default')
    .action(async (options) => {
      await cli.resetSystem(options.name);
    });

  command
    .command('test')
    .description('Test resilience system with simulated operations')
    .option('-n, --name <name>', 'System name', 'default')
    .option('-o, --operations <number>', 'Number of test operations', '10')
    .option('-f, --failure-rate <rate>', 'Failure rate (0.0-1.0)', '0.2')
    .option('-b, --bulkhead <name>', 'Bulkhead name for isolation')
    .action(async (options) => {
      await cli.testSystem({
        systemName: options.name,
        operations: parseInt(options.operations),
        failureRate: parseFloat(options.failureRate),
        bulkheadName: options.bulkhead,
      });
    });

  command
    .command('export')
    .description('Export system configuration')
    .option('-n, --name <name>', 'System name', 'default')
    .option('-o, --output <path>', 'Output file path')
    .action(async (options) => {
      await cli.exportConfig(options.name, options.output);
    });

  return command;
}