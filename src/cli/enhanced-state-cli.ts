#!/usr/bin/env node

import { Command } from 'commander';
import chalk from 'chalk';
import { EnhancedStateManager, FailureArtifact } from '../utils/enhanced-state-manager.js';
import { AEIR } from '@ae-framework/spec-compiler';
import * as fs from 'fs/promises';
import * as path from 'path';

/**
 * Enhanced State Manager CLI
 * Provides command-line interface for advanced state management operations
 */
export class EnhancedStateCLI {
  private stateManager: EnhancedStateManager;

  constructor(projectRoot?: string) {
    this.stateManager = new EnhancedStateManager(projectRoot, {
      enableCompression: true,
      compressionThreshold: 1024,
      defaultTTL: 604800, // 7 days
      gcInterval: 3600, // 1 hour
      maxVersions: 10,
      enableTransactions: true
    });

    // Setup event listeners for better CLI feedback
    this.setupEventListeners();
  }

  /**
   * Initialize the state manager and CLI
   */
  async initialize(): Promise<void> {
    await this.stateManager.initialize();
    console.log(chalk.green('✅ Enhanced State Manager initialized'));
  }

  /**
   * Save SSOT (Single Source of Truth) from file
   */
  async saveSSOT(options: {
    logicalKey: string;
    inputPath: string;
    phase?: string;
    tags?: string;
    ttl?: number;
    source?: string;
  }): Promise<void> {
    try {
      // Load AEIR data from file
      const inputData = await fs.readFile(options.inputPath, 'utf-8');
      const aeir: AEIR = JSON.parse(inputData);

      // Parse tags if provided
      const tags = options.tags ? JSON.parse(options.tags) : {};

      const key = await this.stateManager.saveSSOT(options.logicalKey, aeir, {
        phase: options.phase,
        tags,
        ttl: options.ttl,
        source: options.source
      });

      console.log(chalk.green(`✅ SSOT saved with key: ${key}`));
      console.log(chalk.blue(`   Logical key: ${options.logicalKey}`));
      console.log(chalk.blue(`   Data size: ${JSON.stringify(aeir).length} bytes`));
      
    } catch (error) {
      console.error(chalk.red(`❌ Failed to save SSOT: ${error}`));
      process.exit(1);
    }
  }

  /**
   * Load SSOT data
   */
  async loadSSOT(options: {
    logicalKey: string;
    version?: number;
    outputPath?: string;
  }): Promise<void> {
    try {
      const aeir = await this.stateManager.loadSSOT(options.logicalKey, options.version);
      
      if (!aeir) {
        console.log(chalk.yellow(`⚠️  No data found for logical key: ${options.logicalKey}`));
        return;
      }

      if (options.outputPath) {
        await fs.writeFile(options.outputPath, JSON.stringify(aeir, null, 2));
        console.log(chalk.green(`✅ SSOT data saved to: ${options.outputPath}`));
      } else {
        console.log(chalk.green(`✅ SSOT data loaded:`));
        console.log(JSON.stringify(aeir, null, 2));
      }
      
    } catch (error) {
      console.error(chalk.red(`❌ Failed to load SSOT: ${error}`));
      process.exit(1);
    }
  }

  /**
   * List all versions of a logical key
   */
  async listVersions(logicalKey: string): Promise<void> {
    try {
      const versions = await this.stateManager.getVersions(logicalKey);
      
      if (versions.length === 0) {
        console.log(chalk.yellow(`⚠️  No versions found for logical key: ${logicalKey}`));
        return;
      }

      console.log(chalk.blue(`📋 Versions for ${logicalKey}:`));
      console.log('');
      
      console.log('| Version | Timestamp | Key |');
      console.log('|---------|-----------|-----|');
      
      for (const version of versions) {
        console.log(`| ${version.version} | ${version.timestamp} | ${version.key} |`);
      }
      
    } catch (error) {
      console.error(chalk.red(`❌ Failed to list versions: ${error}`));
      process.exit(1);
    }
  }

  /**
   * Create compressed snapshot
   */
  async createSnapshot(options: {
    phase: string;
    entities?: string;
  }): Promise<void> {
    try {
      const entities = options.entities ? options.entities.split(',').map(s => s.trim()) : undefined;
      const snapshotId = await this.stateManager.createSnapshot(options.phase, entities);
      
      console.log(chalk.green(`✅ Snapshot created: ${snapshotId}`));
      console.log(chalk.blue(`   Phase: ${options.phase}`));
      if (entities) {
        console.log(chalk.blue(`   Entities: ${entities.join(', ')}`));
      }
      
    } catch (error) {
      console.error(chalk.red(`❌ Failed to create snapshot: ${error}`));
      process.exit(1);
    }
  }

  /**
   * Load and display snapshot
   */
  async loadSnapshot(snapshotId: string): Promise<void> {
    try {
      const snapshot = await this.stateManager.loadSnapshot(snapshotId);
      
      if (!snapshot) {
        console.log(chalk.yellow(`⚠️  Snapshot not found: ${snapshotId}`));
        return;
      }

      console.log(chalk.green(`✅ Snapshot loaded: ${snapshotId}`));
      console.log(chalk.blue(`   Entries: ${Object.keys(snapshot).length}`));
      
      console.log('\n📋 Snapshot Contents:');
      for (const [key, entry] of Object.entries(snapshot)) {
        console.log(`  • ${key}: ${entry.logicalKey} (v${entry.version})`);
      }
      
    } catch (error) {
      console.error(chalk.red(`❌ Failed to load snapshot: ${error}`));
      process.exit(1);
    }
  }

  /**
   * Simulate failure artifact for testing
   */
  async simulateFailure(options: {
    phase: string;
    type: 'validation' | 'compilation' | 'test' | 'verification' | 'generation';
    severity: 'low' | 'medium' | 'high' | 'critical';
    message: string;
    retryable?: boolean;
  }): Promise<void> {
    try {
      const artifact: FailureArtifact = {
        id: `failure_${Date.now()}`,
        timestamp: new Date().toISOString(),
        phase: options.phase,
        type: options.type,
        error: new Error(options.message),
        context: {
          simulation: true,
          cli: true,
          timestamp: new Date().toISOString()
        },
        artifacts: [],
        retryable: options.retryable ?? true,
        severity: options.severity
      };

      await this.stateManager.persistFailureArtifact(artifact);
      
      console.log(chalk.red(`🚨 Failure artifact created:`));
      console.log(chalk.blue(`   ID: ${artifact.id}`));
      console.log(chalk.blue(`   Phase: ${artifact.phase}`));
      console.log(chalk.blue(`   Type: ${artifact.type}`));
      console.log(chalk.blue(`   Severity: ${artifact.severity}`));
      console.log(chalk.blue(`   Message: ${options.message}`));
      console.log(chalk.yellow(`   CEGIS trigger emitted via EventBus`));
      
    } catch (error) {
      console.error(chalk.red(`❌ Failed to simulate failure: ${error}`));
      process.exit(1);
    }
  }

  /**
   * Run manual garbage collection
   */
  async runGarbageCollection(): Promise<void> {
    try {
      // Access private method via reflection for CLI purposes
      await (this.stateManager as any).runGarbageCollection();
      console.log(chalk.green('✅ Manual garbage collection completed'));
      
    } catch (error) {
      console.error(chalk.red(`❌ Failed to run garbage collection: ${error}`));
      process.exit(1);
    }
  }

  /**
   * Display storage statistics
   */
  async showStatistics(): Promise<void> {
    try {
      const stats = this.stateManager.getStatistics();
      
      console.log(chalk.blue('📊 Enhanced State Manager Statistics:'));
      console.log('');
      console.log(`Total Entries: ${stats.totalEntries}`);
      console.log(`Total Size: ${this.formatBytes(stats.totalSize)}`);
      console.log(`Compressed Entries: ${stats.compressedEntries} (${Math.round(stats.compressedEntries / stats.totalEntries * 100)}%)`);
      console.log(`Logical Keys: ${stats.logicalKeys}`);
      console.log(`Average Versions per Key: ${stats.averageVersions.toFixed(1)}`);
      console.log(`Oldest Entry: ${stats.oldestEntry || 'N/A'}`);
      console.log(`Newest Entry: ${stats.newestEntry || 'N/A'}`);
      console.log(`Active Transactions: ${stats.activeTransactions}`);
      
    } catch (error) {
      console.error(chalk.red(`❌ Failed to show statistics: ${error}`));
      process.exit(1);
    }
  }

  /**
   * Test transaction functionality
   */
  async testTransaction(): Promise<void> {
    try {
      console.log(chalk.blue('🔄 Testing transaction functionality...'));
      
      const txId = await this.stateManager.beginTransaction();
      console.log(chalk.green(`✅ Transaction started: ${txId}`));
      
      // Create test AEIR data
      const testData: AEIR = {
        version: '1.0.0',
        metadata: {
          name: 'transaction-test',
          created: new Date().toISOString(),
          updated: new Date().toISOString()
        },
        glossary: [],
        domain: [],
        invariants: [],
        usecases: [],
        api: []
      };

      await this.stateManager.saveSSOT('transaction_test', testData, {
        phase: 'test',
        source: 'cli_transaction_test'
      });
      
      await this.stateManager.commitTransaction(txId);
      console.log(chalk.green('✅ Transaction committed successfully'));
      
      // Verify data was saved
      const loadedData = await this.stateManager.loadSSOT('transaction_test');
      if (loadedData) {
        console.log(chalk.green('✅ Transaction test completed successfully'));
      } else {
        console.log(chalk.red('❌ Transaction test failed - data not found'));
      }
      
    } catch (error) {
      console.error(chalk.red(`❌ Transaction test failed: ${error}`));
      process.exit(1);
    }
  }

  /**
   * Export state to file
   */
  async exportState(outputPath: string): Promise<void> {
    try {
      const state = await this.stateManager.exportState();
      await fs.writeFile(outputPath, JSON.stringify(state, null, 2));
      
      console.log(chalk.green(`✅ State exported to: ${outputPath}`));
      console.log(chalk.blue(`   Entries: ${state.entries.length}`));
      console.log(chalk.blue(`   Size: ${this.formatBytes(JSON.stringify(state).length)}`));
      
    } catch (error) {
      console.error(chalk.red(`❌ Failed to export state: ${error}`));
      process.exit(1);
    }
  }

  /**
   * Import state from file
   */
  async importState(inputPath: string): Promise<void> {
    try {
      const data = await fs.readFile(inputPath, 'utf-8');
      const state = JSON.parse(data);
      
      await this.stateManager.importState(state);
      
      console.log(chalk.green(`✅ State imported from: ${inputPath}`));
      console.log(chalk.blue(`   Entries: ${state.entries.length}`));
      
    } catch (error) {
      console.error(chalk.red(`❌ Failed to import state: ${error}`));
      process.exit(1);
    }
  }

  // Private helper methods

  private setupEventListeners(): void {
    this.stateManager.on('ssotSaved', (event) => {
      console.log(chalk.gray(`📁 SSOT saved: ${event.logicalKey} v${event.version}`));
    });

    this.stateManager.on('failureArtifactPersisted', (event) => {
      console.log(chalk.red(`🚨 CEGIS Trigger: ${event.artifact.type} failure in ${event.artifact.phase}`));
    });

    this.stateManager.on('snapshotCreated', (event) => {
      console.log(chalk.blue(`📸 Snapshot created: ${event.snapshotId}`));
    });

    this.stateManager.on('garbageCollectionCompleted', (event) => {
      console.log(chalk.green(`🗑️  GC completed: ${event.expiredCount} entries removed`));
    });

    this.stateManager.on('transactionCommitted', (event) => {
      console.log(chalk.green(`💾 Transaction committed: ${event.txId} (${event.operationCount} ops)`));
    });

    this.stateManager.on('transactionRolledBack', (event) => {
      console.log(chalk.red(`🔄 Transaction rolled back: ${event.txId} (${event.operationCount} ops)`));
    });
  }

  private formatBytes(bytes: number): string {
    const sizes = ['B', 'KB', 'MB', 'GB'];
    if (bytes === 0) return '0 B';
    const i = Math.floor(Math.log(bytes) / Math.log(1024));
    return Math.round(bytes / Math.pow(1024, i)) + ' ' + sizes[i];
  }

  /**
   * Cleanup and shutdown
   */
  async shutdown(): Promise<void> {
    await this.stateManager.shutdown();
    console.log(chalk.green('✅ Enhanced State Manager shutdown complete'));
  }
}

// CLI Command Setup
export function createEnhancedStateCommand(): Command {
  const command = new Command('enhanced-state')
    .description('Enhanced State Manager with SQLite-like storage, compression, and EventBus integration');

  // Save SSOT command
  command
    .command('save')
    .description('Save Single Source of Truth (SSOT) from AE-IR file')
    .requiredOption('-k, --logical-key <key>', 'Logical key for the data')
    .requiredOption('-i, --input <path>', 'Input AE-IR JSON file path')
    .option('-p, --phase <phase>', 'Development phase')
    .option('-t, --tags <json>', 'Tags as JSON object')
    .option('--ttl <seconds>', 'Time to live in seconds', parseInt)
    .option('-s, --source <source>', 'Data source identifier')
    .action(async (options) => {
      const cli = new EnhancedStateCLI();
      await cli.initialize();
      await cli.saveSSOT(options);
      await cli.shutdown();
    });

  // Load SSOT command
  command
    .command('load')
    .description('Load Single Source of Truth (SSOT) data')
    .requiredOption('-k, --logical-key <key>', 'Logical key for the data')
    .option('-v, --version <number>', 'Specific version to load', parseInt)
    .option('-o, --output <path>', 'Output file path')
    .action(async (options) => {
      const cli = new EnhancedStateCLI();
      await cli.initialize();
      await cli.loadSSOT(options);
      await cli.shutdown();
    });

  // List versions command
  command
    .command('versions')
    .description('List all versions of a logical key')
    .requiredOption('-k, --logical-key <key>', 'Logical key to list versions for')
    .action(async (options) => {
      const cli = new EnhancedStateCLI();
      await cli.initialize();
      await cli.listVersions(options.logicalKey);
      await cli.shutdown();
    });

  // Create snapshot command
  command
    .command('snapshot')
    .description('Create compressed snapshot of current state')
    .requiredOption('-p, --phase <phase>', 'Phase to snapshot')
    .option('-e, --entities <entities>', 'Comma-separated list of entities to include')
    .action(async (options) => {
      const cli = new EnhancedStateCLI();
      await cli.initialize();
      await cli.createSnapshot(options);
      await cli.shutdown();
    });

  // Load snapshot command
  command
    .command('load-snapshot')
    .description('Load and display snapshot contents')
    .requiredOption('-s, --snapshot-id <id>', 'Snapshot ID to load')
    .action(async (options) => {
      const cli = new EnhancedStateCLI();
      await cli.initialize();
      await cli.loadSnapshot(options.snapshotId);
      await cli.shutdown();
    });

  // Simulate failure command
  command
    .command('simulate-failure')
    .description('Simulate failure artifact for CEGIS testing')
    .requiredOption('-p, --phase <phase>', 'Phase where failure occurred')
    .requiredOption('-t, --type <type>', 'Failure type (validation|compilation|test|verification|generation)')
    .requiredOption('-m, --message <message>', 'Error message')
    .option('-s, --severity <severity>', 'Failure severity (low|medium|high|critical)', 'medium')
    .option('--retryable', 'Mark as retryable failure')
    .action(async (options) => {
      const cli = new EnhancedStateCLI();
      await cli.initialize();
      await cli.simulateFailure(options);
      await cli.shutdown();
    });

  // Garbage collection command
  command
    .command('gc')
    .description('Run manual garbage collection')
    .action(async () => {
      const cli = new EnhancedStateCLI();
      await cli.initialize();
      await cli.runGarbageCollection();
      await cli.shutdown();
    });

  // Statistics command
  command
    .command('stats')
    .description('Display storage statistics')
    .action(async () => {
      const cli = new EnhancedStateCLI();
      await cli.initialize();
      await cli.showStatistics();
      await cli.shutdown();
    });

  // Transaction test command
  command
    .command('test-tx')
    .description('Test transaction functionality')
    .action(async () => {
      const cli = new EnhancedStateCLI();
      await cli.initialize();
      await cli.testTransaction();
      await cli.shutdown();
    });

  // Export state command
  command
    .command('export')
    .description('Export state to file')
    .requiredOption('-o, --output <path>', 'Output file path')
    .action(async (options) => {
      const cli = new EnhancedStateCLI();
      await cli.initialize();
      await cli.exportState(options.output);
      await cli.shutdown();
    });

  // Import state command
  command
    .command('import')
    .description('Import state from file')
    .requiredOption('-i, --input <path>', 'Input file path')
    .action(async (options) => {
      const cli = new EnhancedStateCLI();
      await cli.initialize();
      await cli.importState(options.input);
      await cli.shutdown();
    });

  return command;
}