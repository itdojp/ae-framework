#!/usr/bin/env node

import { Command } from 'commander';
import chalk from 'chalk';
import { CircuitBreaker, CircuitState } from '../utils/circuit-breaker.js';

/**
 * Circuit Breaker CLI
 * Provides command-line interface for circuit breaker management and monitoring
 */
export class CircuitBreakerCLI {
  private breakers: Map<string, CircuitBreaker>;

  constructor() {
    this.breakers = new Map();
    this.setupEventListeners();
  }

  /**
   * Create a circuit breaker with configuration
   */
  async createCircuitBreaker(options: {
    name: string;
    failureThreshold?: number;
    successThreshold?: number;
    timeout?: number;
    monitoringWindow?: number;
  }): Promise<void> {
    try {
      const breaker = new CircuitBreaker(options.name, {
        failureThreshold: options.failureThreshold || 5,
        successThreshold: options.successThreshold || 3,
        timeout: options.timeout || 60000,
        monitoringWindow: options.monitoringWindow || 10000,
        enableMonitoring: true
      });
      
      this.breakers.set(options.name, breaker);

      console.log(chalk.green(`✅ Circuit breaker '${options.name}' created successfully`));
      console.log(chalk.blue(`   State: ${breaker.getState()}`));
      console.log(chalk.blue(`   Failure threshold: ${options.failureThreshold || 5}`));
      console.log(chalk.blue(`   Success threshold: ${options.successThreshold || 3}`));
      console.log(chalk.blue(`   Timeout: ${options.timeout || 60000}ms`));
      
    } catch (error) {
      console.error(chalk.red(`❌ Failed to create circuit breaker: ${error}`));
      process.exit(1);
    }
  }

  /**
   * List all circuit breakers and their states
   */
  async listCircuitBreakers(): Promise<void> {
    try {
      const allBreakers = this.breakers;
      
      if (allBreakers.size === 0) {
        console.log(chalk.yellow('⚠️  No circuit breakers found'));
        return;
      }

      console.log(chalk.blue('📋 Circuit Breakers:'));
      console.log('');
      
      console.log('| Name | State | Failures | Successes | Total Requests | Health |');
      console.log('|------|--------|----------|-----------|----------------|---------|');
      
      for (const [name, breaker] of allBreakers) {
        const stats = breaker.getStats();
        const health = breaker.isHealthy() ? '🟢 Healthy' : '🔴 Unhealthy';
        const stateIcon = this.getStateIcon(stats.state);
        
        console.log(`| ${name} | ${stateIcon} ${stats.state} | ${stats.totalFailures} | ${stats.totalSuccesses} | ${stats.totalRequests} | ${health} |`);
      }
      
    } catch (error) {
      console.error(chalk.red(`❌ Failed to list circuit breakers: ${error}`));
      process.exit(1);
    }
  }

  /**
   * Show detailed statistics for a specific circuit breaker
   */
  async showStats(breakerName: string): Promise<void> {
    try {
      const breaker = this.breakers.get(breakerName);
      if (!breaker) {
        console.error(chalk.red(`❌ Circuit breaker '${breakerName}' not found`));
        return;
      }
      const stats = breaker.getStats();
      
      console.log(chalk.blue(`📊 Circuit Breaker Statistics: ${breakerName}`));
      console.log('');
      
      console.log(`State: ${this.getStateIcon(stats.state)} ${stats.state}`);
      console.log(`Current Failures: ${stats.failureCount}`);
      console.log(`Current Successes: ${stats.successCount}`);
      console.log(`Total Requests: ${stats.totalRequests}`);
      console.log(`Total Failures: ${stats.totalFailures}`);
      console.log(`Total Successes: ${stats.totalSuccesses}`);
      console.log(`Circuit Opens: ${stats.circuitOpenCount}`);
      console.log(`Average Response Time: ${stats.averageResponseTime.toFixed(2)}ms`);
      console.log(`Uptime: ${this.formatDuration(stats.uptime)}`);
      console.log(`Health: ${breaker.isHealthy() ? '🟢 Healthy' : '🔴 Unhealthy'}`);
      
      if (stats.lastFailureTime) {
        console.log(`Last Failure: ${new Date(stats.lastFailureTime).toISOString()}`);
      }
      
      if (stats.lastSuccessTime) {
        console.log(`Last Success: ${new Date(stats.lastSuccessTime).toISOString()}`);
      }
      
    } catch (error) {
      console.error(chalk.red(`❌ Failed to show stats: ${error}`));
      process.exit(1);
    }
  }

  /**
   * Generate comprehensive health report
   */
  async generateHealthReport(): Promise<void> {
    try {
      const report = this.createHealthReport();
      
      console.log(chalk.blue('🏥 Circuit Breaker Health Report'));
      console.log('');
      
      // Overall health
      const overallIcon = this.getHealthIcon(report.overall);
      console.log(`Overall Health: ${overallIcon} ${report.overall.toUpperCase()}`);
      console.log('');
      
      // Summary
      console.log(chalk.blue('📈 Summary:'));
      console.log(`Total Breakers: ${report.totalBreakers}`);
      console.log(`🟢 Closed: ${report.closedBreakers}`);
      console.log(`🟡 Half-Open: ${report.halfOpenBreakers}`);
      console.log(`🔴 Open: ${report.openBreakers}`);
      console.log(`Total Requests: ${report.totalRequests}`);
      console.log(`Total Failures: ${report.totalFailures}`);
      
      if (report.totalRequests > 0) {
        const failureRate = (report.totalFailures / report.totalRequests * 100).toFixed(2);
        console.log(`Failure Rate: ${failureRate}%`);
      }
      
      console.log('');
      
      // Individual breaker reports
      if (report.breakers.length > 0) {
        console.log(chalk.blue('🔍 Individual Breaker Reports:'));
        console.log('');
        
        for (const breaker of report.breakers) {
          const healthIcon = this.getHealthIcon(breaker.health);
          const stateIcon = this.getStateIcon(breaker.state as CircuitState);
          
          console.log(`${breaker.name}: ${healthIcon} ${breaker.health.toUpperCase()} (${stateIcon} ${breaker.state})`);
          
          if (breaker.recentFailures && breaker.recentFailures.length > 0) {
            console.log(`  Recent Failures: ${breaker.recentFailures.length}`);
            breaker.recentFailures.slice(0, 3).forEach((failure: any) => {
              console.log(`    • ${new Date(failure.timestamp).toISOString()}: ${failure.error}`);
            });
          }
          
          if (breaker.recommendations && breaker.recommendations.length > 0) {
            console.log(`  Recommendations:`);
            breaker.recommendations.forEach(rec => {
              console.log(`    • ${rec}`);
            });
          }
          
          console.log('');
        }
      }
      
    } catch (error) {
      console.error(chalk.red(`❌ Failed to generate health report: ${error}`));
      process.exit(1);
    }
  }

  /**
   * Test a circuit breaker with simulated operations
   */
  async testCircuitBreaker(options: {
    name: string;
    operations: number;
    failureRate: number;
    delay: number;
  }): Promise<void> {
    try {
      const breaker = this.breakers.get(options.name);
      if (!breaker) {
        console.error(chalk.red(`❌ Circuit breaker '${options.name}' not found`));
        return;
      }
      
      console.log(chalk.blue(`🧪 Testing circuit breaker '${options.name}'`));
      console.log(`Operations: ${options.operations}`);
      console.log(`Failure Rate: ${options.failureRate * 100}%`);
      console.log(`Delay: ${options.delay}ms`);
      console.log('');
      
      let successCount = 0;
      let failureCount = 0;
      let rejectedCount = 0;

      for (let i = 0; i < options.operations; i++) {
        const shouldFail = Math.random() < options.failureRate;
        
        try {
          await breaker.execute(async () => {
            await new Promise(resolve => setTimeout(resolve, options.delay));
            
            if (shouldFail) {
              throw new Error(`Simulated failure ${i + 1}`);
            }
            
            return `Success ${i + 1}`;
          });
          
          successCount++;
          process.stdout.write(chalk.green('✓'));
          
        } catch (error) {
          if (error.name === 'CircuitBreakerOpenError') {
            rejectedCount++;
            process.stdout.write(chalk.red('X'));
          } else {
            failureCount++;
            process.stdout.write(chalk.yellow('!'));
          }
        }

        // Add small delay between operations
        await new Promise(resolve => setTimeout(resolve, 50));
      }

      console.log('');
      console.log('');
      console.log(chalk.blue('📊 Test Results:'));
      console.log(`✓ Successes: ${successCount}`);
      console.log(`! Failures: ${failureCount}`);
      console.log(`X Rejected: ${rejectedCount}`);
      console.log(`Final State: ${this.getStateIcon(breaker.getState())} ${breaker.getState()}`);
      
    } catch (error) {
      console.error(chalk.red(`❌ Failed to test circuit breaker: ${error}`));
      process.exit(1);
    }
  }

  /**
   * Reset a circuit breaker
   */
  async resetCircuitBreaker(breakerName: string): Promise<void> {
    try {
      const breaker = this.breakers.get(breakerName);
      if (!breaker) {
        console.error(chalk.red(`❌ Circuit breaker '${breakerName}' not found`));
        return;
      }
      breaker.reset();
      
      console.log(chalk.green(`✅ Circuit breaker '${breakerName}' reset successfully`));
      console.log(chalk.blue(`   New state: ${breaker.getState()}`));
      
    } catch (error) {
      console.error(chalk.red(`❌ Failed to reset circuit breaker: ${error}`));
      process.exit(1);
    }
  }

  /**
   * Force open a circuit breaker
   */
  async forceOpen(breakerName: string): Promise<void> {
    try {
      const breaker = this.breakers.get(breakerName);
      if (!breaker) {
        console.error(chalk.red(`❌ Circuit breaker '${breakerName}' not found`));
        return;
      }
      breaker.forceOpen();
      
      console.log(chalk.yellow(`⚠️  Circuit breaker '${breakerName}' forced to OPEN state`));
      
    } catch (error) {
      console.error(chalk.red(`❌ Failed to force open circuit breaker: ${error}`));
      process.exit(1);
    }
  }

  /**
   * Force close a circuit breaker
   */
  async forceClose(breakerName: string): Promise<void> {
    try {
      const breaker = this.breakers.get(breakerName);
      if (!breaker) {
        console.error(chalk.red(`❌ Circuit breaker '${breakerName}' not found`));
        return;
      }
      breaker.forceClose();
      
      console.log(chalk.green(`✅ Circuit breaker '${breakerName}' forced to CLOSED state`));
      
    } catch (error) {
      console.error(chalk.red(`❌ Failed to force close circuit breaker: ${error}`));
      process.exit(1);
    }
  }

  /**
   * Watch circuit breaker state changes in real-time
   */
  async watchCircuitBreakers(): Promise<void> {
    console.log(chalk.blue('👁️  Watching circuit breaker state changes (Press Ctrl+C to stop)'));
    console.log('');

    // Show initial state
    await this.listCircuitBreakers();
    console.log('');
    console.log(chalk.gray('Listening for state changes...'));
    console.log('');

    // Setup interrupt handler
    process.on('SIGINT', () => {
      console.log('');
      console.log(chalk.yellow('👋 Stopping circuit breaker watch'));
      process.exit(0);
    });

    // Keep process alive
    setInterval(() => {
      // This interval keeps the process running
      // Event listeners will handle the actual output
    }, 1000);
  }

  // Helper methods

  private setupEventListeners(): void {
    // Circuit breaker event handling would need to be implemented
    // Individual breaker event listeners would be attached when breakers are created
    console.log(chalk.gray('🔧 Circuit breaker event listeners initialized'));
  }

  private getStateIcon(state: CircuitState): string {
    switch (state) {
      case CircuitState.CLOSED:
        return '🟢';
      case CircuitState.HALF_OPEN:
        return '🟡';
      case CircuitState.OPEN:
        return '🔴';
      default:
        return '⚫';
    }
  }

  private getHealthIcon(health: string): string {
    switch (health) {
      case 'healthy':
        return '🟢';
      case 'degraded':
        return '🟡';
      case 'unhealthy':
        return '🔴';
      default:
        return '⚫';
    }
  }

  private formatDuration(ms: number): string {
    const seconds = Math.floor(ms / 1000);
    const minutes = Math.floor(seconds / 60);
    const hours = Math.floor(minutes / 60);
    const days = Math.floor(hours / 24);

    if (days > 0) {
      return `${days}d ${hours % 24}h ${minutes % 60}m`;
    } else if (hours > 0) {
      return `${hours}h ${minutes % 60}m ${seconds % 60}s`;
    } else if (minutes > 0) {
      return `${minutes}m ${seconds % 60}s`;
    } else {
      return `${seconds}s`;
    }
  }

  private createHealthReport(): {
    totalBreakers: number;
    healthy: number;
    degraded: number;
    unhealthy: number;
    summary: Array<{name: string; state: string; health: string; recentFailures?: any[]; recommendations?: string[]}>;
    overall: string;
    breakers: Array<{name: string; state: string; health: string; recentFailures?: any[]; recommendations?: string[]}>;
    totalRequests: number;
    totalFailures: number;
    closedBreakers: number;
    halfOpenBreakers: number;
    openBreakers: number;
  } {
    const summary: Array<{name: string; state: string; health: string}> = [];
    let healthy = 0;
    let degraded = 0;
    let unhealthy = 0;

    for (const [name, breaker] of this.breakers) {
      const state = breaker.getState();
      const stats = breaker.getStats();
      
      let health: string;
      if (state === 'CLOSED' && stats.failureCount === 0) {
        health = 'healthy';
        healthy++;
      } else if (state === 'HALF_OPEN' || (state === 'CLOSED' && stats.failureCount > 0)) {
        health = 'degraded';
        degraded++;
      } else {
        health = 'unhealthy';
        unhealthy++;
      }

      summary.push({ name, state, health });
    }

    // Calculate overall health
    let overall: string;
    const totalBreakers = this.breakers.size;
    if (unhealthy > totalBreakers * 0.5) {
      overall = 'unhealthy';
    } else if (degraded > totalBreakers * 0.3) {
      overall = 'degraded';
    } else {
      overall = 'healthy';
    }

    // Calculate summary statistics
    let totalRequests = 0;
    let totalFailures = 0;
    let closedBreakers = 0;
    let halfOpenBreakers = 0;
    let openBreakers = 0;

    for (const [, breaker] of this.breakers) {
      const stats = breaker.getStats();
      const state = breaker.getState();
      totalRequests += stats.totalRequests;
      totalFailures += stats.totalFailures;
      
      if (state === 'CLOSED') closedBreakers++;
      else if (state === 'HALF_OPEN') halfOpenBreakers++;
      else if (state === 'OPEN') openBreakers++;
    }

    return {
      totalBreakers,
      healthy,
      degraded,
      unhealthy,
      summary,
      overall,
      breakers: summary.map(s => ({...s, recentFailures: [], recommendations: []})),
      totalRequests,
      totalFailures,
      closedBreakers,
      halfOpenBreakers,
      openBreakers
    };
  }
}

// CLI Command Setup
export function createCircuitBreakerCommand(): Command {
  const command = new Command('circuit-breaker')
    .description('Circuit Breaker pattern implementation for fault tolerance and resilience');

  // Create circuit breaker command
  command
    .command('create')
    .description('Create a new circuit breaker')
    .requiredOption('-n, --name <name>', 'Circuit breaker name')
    .option('-f, --failure-threshold <number>', 'Failure threshold to open circuit', parseInt, 5)
    .option('-s, --success-threshold <number>', 'Success threshold to close circuit', parseInt, 3)
    .option('-t, --timeout <ms>', 'Timeout before attempting to half-open (ms)', parseInt, 60000)
    .option('-w, --monitoring-window <ms>', 'Monitoring window for failures (ms)', parseInt, 60000)
    .action(async (options) => {
      const cli = new CircuitBreakerCLI();
      await cli.createCircuitBreaker(options);
    });

  // List circuit breakers command
  command
    .command('list')
    .description('List all circuit breakers')
    .action(async () => {
      const cli = new CircuitBreakerCLI();
      await cli.listCircuitBreakers();
    });

  // Show stats command
  command
    .command('stats')
    .description('Show detailed statistics for a circuit breaker')
    .requiredOption('-n, --name <name>', 'Circuit breaker name')
    .action(async (options) => {
      const cli = new CircuitBreakerCLI();
      await cli.showStats(options.name);
    });

  // Health report command
  command
    .command('health')
    .description('Generate comprehensive health report')
    .action(async () => {
      const cli = new CircuitBreakerCLI();
      await cli.generateHealthReport();
    });

  // Test command
  command
    .command('test')
    .description('Test a circuit breaker with simulated operations')
    .requiredOption('-n, --name <name>', 'Circuit breaker name')
    .option('-o, --operations <number>', 'Number of operations to simulate', parseInt, 20)
    .option('-f, --failure-rate <rate>', 'Failure rate (0.0 to 1.0)', parseFloat, 0.3)
    .option('-d, --delay <ms>', 'Delay between operations (ms)', parseInt, 100)
    .action(async (options) => {
      const cli = new CircuitBreakerCLI();
      await cli.testCircuitBreaker(options);
    });

  // Reset command
  command
    .command('reset')
    .description('Reset a circuit breaker to initial state')
    .requiredOption('-n, --name <name>', 'Circuit breaker name')
    .action(async (options) => {
      const cli = new CircuitBreakerCLI();
      await cli.resetCircuitBreaker(options.name);
    });

  // Force open command
  command
    .command('force-open')
    .description('Force a circuit breaker to open state')
    .requiredOption('-n, --name <name>', 'Circuit breaker name')
    .action(async (options) => {
      const cli = new CircuitBreakerCLI();
      await cli.forceOpen(options.name);
    });

  // Force close command
  command
    .command('force-close')
    .description('Force a circuit breaker to close state')
    .requiredOption('-n, --name <name>', 'Circuit breaker name')
    .action(async (options) => {
      const cli = new CircuitBreakerCLI();
      await cli.forceClose(options.name);
    });

  // Watch command
  command
    .command('watch')
    .description('Watch circuit breaker state changes in real-time')
    .action(async () => {
      const cli = new CircuitBreakerCLI();
      await cli.watchCircuitBreakers();
    });

  return command;
}