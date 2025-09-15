/**
 * Quality CLI commands for the AE-Framework
 * Provides commands to execute and manage quality gates
 */

import { Command } from 'commander';
import chalk from 'chalk';
import { QualityPolicyLoader, qualityPolicy } from '../quality/policy-loader.js';
import { toMessage } from '../utils/error-utils.js';
import { safeExit } from '../utils/safe-exit.js';
import { QualityGateRunner } from '../quality/quality-gate-runner.js';
import * as fs from 'fs';
import * as path from 'path';

export function createQualityCommand(): Command {
  const quality = new Command('quality');
  quality.description('Quality gates and policy management');

  // Run quality gates
  quality
    .command('run')
    .description('Execute quality gates for current environment')
    .option('-e, --env <environment>', 'Target environment', process.env['NODE_ENV'] || 'development')
    .option('-g, --gates <gates>', 'Comma-separated list of specific gates to run')
    .option('--sequential', 'Run gates sequentially instead of in parallel')
    .option('--dry-run', 'Show what would be executed without running')
    .option('-v, --verbose', 'Verbose output with detailed results')
    .option('-t, --timeout <ms>', 'Timeout for each gate in milliseconds', '300000')
    .option('-o, --output <dir>', 'Output directory for reports', 'reports/quality-gates')
    .action(async (options) => {
      try {
        console.log(chalk.blue(`🔍 Running quality gates for ${options.env} environment`));
        
        const runner = new QualityGateRunner();
        const report = await runner.executeGates({
          environment: options.env,
          gates: options.gates ? options.gates.split(',').map((g: string) => g.trim()) : undefined,
          parallel: !options.sequential,
          dryRun: options.dryRun,
          verbose: options.verbose,
          timeout: parseInt(options.timeout),
          outputDir: options.output,
        });

        // Exit with appropriate code
        if (report.summary.blockers.length > 0) {
          console.log(chalk.red(`\n❌ ${report.summary.blockers.length} blocking quality gate(s) failed`));
          safeExit(1);
        } else if (report.failedGates > 0) {
          console.log(chalk.yellow(`\n⚠️  ${report.failedGates} quality gate(s) failed (non-blocking)`));
        } else {
          console.log(chalk.green('\n✅ All quality gates passed!'));
        }
      } catch (error: unknown) {
        console.error(chalk.red(`❌ Error running quality gates: ${toMessage(error)}`));
        safeExit(1);
      }
    });

  // List available quality gates
  quality
    .command('list')
    .description('List available quality gates and their configuration')
    .option('-e, --env <environment>', 'Show configuration for specific environment', 'development')
    .option('--all', 'Show all gates regardless of environment')
    .option('--format <format>', 'Output format (table, json, summary)', 'table')
    .action(async (options) => {
      try {
        const gates = options.all 
          ? Object.values(qualityPolicy.getAllGates())
          : qualityPolicy.getGatesForEnvironment(options.env);

        if (options.format === 'json') {
          console.log(JSON.stringify(gates, null, 2));
          return;
        }

        console.log(chalk.blue(`📋 Quality Gates for ${options.env} environment\n`));
        
        if (gates.length === 0) {
          console.log(chalk.yellow('No quality gates found for this environment'));
          return;
        }

        if (options.format === 'summary') {
          gates.forEach(gate => {
            // Find the gate key in policy
            const allGates = qualityPolicy.getAllGates();
            const gateKey = Object?.keys(allGates)?.find(key => allGates[key]?.name === gate?.name) || gate?.name;
            
            const threshold = qualityPolicy.getThreshold(gateKey, options.env);
            const shouldBlock = qualityPolicy.shouldBlock(gateKey, options.env);
            
            console.log(chalk.cyan(`${gate.name}:`));
            console.log(`  Description: ${gate.description}`);
            console.log(`  Category: ${gate.category}`);
            console.log(`  Enabled: ${gate.enabled ? '✅' : '❌'}`);
            console.log(`  Blocking: ${shouldBlock ? '🚫' : '⚠️ '}`);
            console.log(`  Command: ${gate.commands.test}`);
            console.log();
          });
        } else {
          // Table format
          console.log('Name'.padEnd(20) + 'Category'.padEnd(15) + 'Enabled'.padEnd(10) + 'Blocking'.padEnd(10) + 'Description');
          console.log('-'.repeat(80));
          
          gates.forEach(gate => {
            // Find the gate key in policy
            const allGates = qualityPolicy.getAllGates();
            const gateKey = Object?.keys(allGates)?.find(key => allGates[key]?.name === gate?.name) || gate?.name;
            
            const shouldBlock = qualityPolicy.shouldBlock(gateKey, options.env);
            const enabled = gate.enabled ? '✅' : '❌';
            const blocking = shouldBlock ? '🚫' : '⚠️ ';
            
            console.log(
              gate.name.padEnd(20) +
              gate.category.padEnd(15) +
              enabled.padEnd(10) +
              blocking.padEnd(10) +
              gate.description.substring(0, 40) + (gate.description.length > 40 ? '...' : '')
            );
          });
        }
      } catch (error: unknown) {
        console.error(chalk.red(`❌ Error listing quality gates: ${toMessage(error)}`));
        safeExit(1);
      }
    });

  // Show policy configuration
  quality
    .command('policy')
    .description('Show quality policy configuration')
    .option('-e, --env <environment>', 'Show specific environment configuration')
    .option('-g, --gate <gate>', 'Show specific gate configuration')
    .option('--format <format>', 'Output format (json, yaml, summary)', 'summary')
    .action(async (options) => {
      try {
        if (options.gate) {
          // Show specific gate
          const gates = qualityPolicy.getAllGates();
          const gate = gates[options.gate];
          
          if (!gate) {
            console.error(chalk.red(`❌ Quality gate '${options.gate}' not found`));
            safeExit(1);
          }

          console.log(chalk.blue(`📋 Quality Gate: ${gate.name}\n`));
          console.log(JSON.stringify(gate, null, 2));
          
        } else if (options.env) {
          // Show environment configuration
          const envConfig = qualityPolicy.getEnvironmentConfig(options.env);
          const gates = qualityPolicy.getGatesForEnvironment(options.env);
          
          console.log(chalk.blue(`🌍 Environment: ${options.env}\n`));
          console.log(`Description: ${envConfig.description}`);
          console.log(`Enforcement Level: ${envConfig.enforcementLevel}`);
          console.log(`Quality Gates: ${gates.length}`);
          console.log(`Gate Names: ${gates.map(g => g.name).join(', ')}`);
          
        } else {
          // Show full policy
          const allowed: Array<'json' | 'yaml' | 'summary'> = ['json', 'yaml', 'summary'];
          const fmt = allowed.includes(options.format) ? options.format as 'json' | 'yaml' | 'summary' : 'json';
          const policy = qualityPolicy.exportPolicy(fmt);
          console.log(policy);
        }
      } catch (error: unknown) {
        console.error(chalk.red(`❌ Error showing policy: ${toMessage(error)}`));
        safeExit(1);
      }
    });

  // Validate policy configuration
  quality
    .command('validate')
    .description('Validate quality policy configuration')
    .option('--fix', 'Attempt to fix validation issues')
    .action(async (options) => {
      try {
        console.log(chalk.blue('🔍 Validating quality policy configuration...'));
        
        // Load and validate policy
        const policy = qualityPolicy.loadPolicy();
        
        const issues: string[] = [];
        
        // Check for missing commands
        Object.entries(policy.qualityGates).forEach(([name, gate]) => {
          if (!gate.commands.test) {
            issues.push(`Gate '${name}' missing test command`);
          }
        });

        // Check for missing thresholds
        Object.entries(policy.qualityGates).forEach(([name, gate]) => {
          Object.keys(policy.environments).forEach(env => {
            if (!gate.thresholds[env]) {
              issues.push(`Gate '${name}' missing threshold for environment '${env}'`);
            }
          });
        });

        // Check composite gate references
        Object.entries(policy.compositeGates).forEach(([name, composite]) => {
          composite.gates.forEach(gateName => {
            if (!policy.qualityGates[gateName]) {
              issues.push(`Composite gate '${name}' references unknown gate '${gateName}'`);
            }
          });
        });

        if (issues.length === 0) {
          console.log(chalk.green('✅ Quality policy configuration is valid'));
        } else {
          console.log(chalk.yellow(`⚠️  Found ${issues.length} validation issues:`));
          issues.forEach(issue => {
            console.log(chalk.yellow(`   • ${issue}`));
          });
          
          if (options.fix) {
            console.log(chalk.blue('\n🔧 Attempting to fix issues...'));
            // Implement basic fixes here
            console.log(chalk.yellow('⚠️  Automatic fixes not yet implemented'));
          }
        }
        
      } catch (error: unknown) {
        console.error(chalk.red(`❌ Error validating policy: ${toMessage(error)}`));
        safeExit(1);
      }
    });

  // Show quality reports
  quality
    .command('report')
    .description('Show quality gate reports')
    .option('-e, --env <environment>', 'Environment to show reports for', 'development')
    .option('-l, --latest', 'Show only the latest report')
    .option('-d, --days <days>', 'Show reports from last N days', '7')
    .option('--format <format>', 'Output format (json, summary)', 'summary')
    .action(async (options) => {
      try {
        const reportsDir = path.join(process.cwd(), 'reports', 'quality-gates');
        
        if (!fs.existsSync(reportsDir)) {
          console.log(chalk.yellow('⚠️  No quality reports found'));
          return;
        }

        if (options.latest) {
          // Show latest report
          const latestFile = path.join(reportsDir, `quality-report-${options.env}-latest.json`);
          
          if (!fs.existsSync(latestFile)) {
            console.log(chalk.yellow(`⚠️  No latest report found for environment '${options.env}'`));
            return;
          }

          const report = JSON.parse(fs.readFileSync(latestFile, 'utf8'));
          
          if (options.format === 'json') {
            console.log(JSON.stringify(report, null, 2));
          } else {
            console.log(chalk.blue(`📊 Latest Quality Report - ${options.env}\n`));
            console.log(`Timestamp: ${report.timestamp}`);
            console.log(`Overall Score: ${report.overallScore}/100`);
            console.log(`Gates Passed: ${report.passedGates}/${report.totalGates}`);
            console.log(`Execution Time: ${Math.round(report.summary.executionTime / 1000)}s`);
            
            if (report.summary.blockers.length > 0) {
              console.log(chalk.red(`\nBlockers: ${report.summary.blockers.join(', ')}`));
            }
          }
        } else {
          // List available reports
          const files = fs.readdirSync(reportsDir)
            .filter(f => f.startsWith(`quality-report-${options.env}-`) && f.endsWith('.json') && !f.includes('latest'))
            .sort()
            .reverse();

          const dayFilter = parseInt(options.days);
          const cutoffDate = new Date(Date.now() - dayFilter * 24 * 60 * 60 * 1000);

          console.log(chalk.blue(`📋 Quality Reports for ${options.env} (last ${options.days} days)\n`));
          
          files.forEach(file => {
            const filePath = path.join(reportsDir, file);
            const stats = fs.statSync(filePath);
            
            if (stats.mtime >= cutoffDate) {
              const report = JSON.parse(fs.readFileSync(filePath, 'utf8'));
              const timestamp = new Date(report.timestamp).toLocaleString();
              const score = report.overallScore;
              const status = report.failedGates === 0 ? '✅' : (report.summary.blockers.length > 0 ? '❌' : '⚠️ ');
              
              console.log(`${status} ${timestamp} - Score: ${score}/100 (${report.passedGates}/${report.totalGates} gates)`);
            }
          });
        }
      } catch (error: unknown) {
        console.error(chalk.red(`❌ Error showing reports: ${toMessage(error)}`));
        safeExit(1);
      }
    });

  // Initialize quality configuration
  quality
    .command('init')
    .description('Initialize quality policy configuration')
    .option('--force', 'Overwrite existing configuration')
    .action(async (options) => {
      try {
        const configPath = path.join(process.cwd(), 'config', 'quality-policy.json');
        
        if (fs.existsSync(configPath) && !options.force) {
          console.log(chalk.yellow('⚠️  Quality policy already exists. Use --force to overwrite.'));
          return;
        }

        // Ensure config directory exists
        const configDir = path.dirname(configPath);
        if (!fs.existsSync(configDir)) {
          fs.mkdirSync(configDir, { recursive: true });
        }

        console.log(chalk.blue('🔧 Initializing quality policy configuration...'));
        console.log(`📁 Creating: ${configPath}`);
        
        // The config is already created in the file, just confirm it exists
        if (fs.existsSync(configPath)) {
          console.log(chalk.green('✅ Quality policy configuration initialized successfully'));
          console.log(chalk.cyan('\nNext steps:'));
          console.log('  • Review and customize the policy in config/quality-policy.json');
          console.log('  • Run "npm run quality:run" to execute quality gates');
          console.log('  • Add quality gates to your CI/CD pipeline');
        } else {
          console.log(chalk.red('❌ Failed to create quality policy configuration'));
          safeExit(1);
        }
      } catch (error: unknown) {
        console.error(chalk.red(`❌ Error initializing quality configuration: ${toMessage(error)}`));
        safeExit(1);
      }
    });

  return quality;
}

export default createQualityCommand;
