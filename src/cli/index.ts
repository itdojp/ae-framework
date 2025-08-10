#!/usr/bin/env node

import { Command } from 'commander';
import chalk from 'chalk';
import { PhaseValidator } from './validators/PhaseValidator';
import { GuardRunner } from './guards/GuardRunner';
import { ConfigLoader } from './config/ConfigLoader';
import { MetricsCollector } from './metrics/MetricsCollector';
import { AEFrameworkConfig, Phase, Guard } from './types';

const program = new Command();

class AEFrameworkCLI {
  private config: AEFrameworkConfig;
  private phaseValidator: PhaseValidator;
  private guardRunner: GuardRunner;
  private metricsCollector: MetricsCollector;

  constructor() {
    this.config = ConfigLoader.load();
    this.phaseValidator = new PhaseValidator(this.config);
    this.guardRunner = new GuardRunner(this.config);
    this.metricsCollector = new MetricsCollector(this.config);
  }

  async checkPhase(phaseName: string): Promise<void> {
    console.log(chalk.blue(`🔍 Checking phase: ${phaseName}`));
    
    const phase = this.config.phases[phaseName];
    if (!phase) {
      console.log(chalk.red(`❌ Unknown phase: ${phaseName}`));
      process.exit(1);
    }

    const results = await this.phaseValidator.validate(phase);
    
    if (results.success) {
      console.log(chalk.green(`✅ Phase ${phaseName} validation passed`));
      this.displayResults(results.details);
      console.log(chalk.green(`⏭️  Ready for next phase`));
    } else {
      console.log(chalk.red(`❌ Phase ${phaseName} validation failed`));
      this.displayResults(results.details);
      process.exit(1);
    }
  }

  async runGuards(guardName?: string): Promise<void> {
    const guards = guardName 
      ? [this.config.guards.find(g => g.name === guardName)].filter(Boolean)
      : this.config.guards;

    if (guards.length === 0) {
      console.log(chalk.yellow(`⚠️  No guards found`));
      return;
    }

    console.log(chalk.blue(`🛡️  Running ${guards.length} guards...`));

    let allPassed = true;
    for (const guard of guards) {
      const result = await this.guardRunner.run(guard!);
      
      if (result.success) {
        console.log(chalk.green(`✅ ${guard!.name}: PASSED`));
      } else {
        console.log(chalk.red(`❌ ${guard!.name}: FAILED`));
        console.log(chalk.red(`   ${result.message}`));
        
        if (guard!.enforcement === 'strict') {
          allPassed = false;
        }
      }
    }

    if (!allPassed) {
      process.exit(1);
    }
  }

  async nextPhase(): Promise<void> {
    const currentPhase = await this.detectCurrentPhase();
    const nextPhase = this.getNextPhase(currentPhase);
    
    if (!nextPhase) {
      console.log(chalk.green(`🎉 All phases completed!`));
      return;
    }

    console.log(chalk.blue(`📋 Current phase: ${currentPhase}`));
    console.log(chalk.blue(`⏭️  Next phase: ${nextPhase}`));

    // Validate prerequisites
    const phase = this.config.phases[nextPhase];
    if (phase.prerequisites) {
      for (const prereq of phase.prerequisites) {
        const valid = await this.phaseValidator.validatePrerequisite(prereq);
        if (!valid.success) {
          console.log(chalk.red(`❌ Prerequisite not met: ${prereq.phase}`));
          console.log(chalk.red(`   ${valid.message}`));
          process.exit(1);
        }
      }
    }

    console.log(chalk.green(`✅ Prerequisites satisfied`));
    console.log(chalk.blue(`🚀 Ready to start phase: ${nextPhase}`));
    this.displayPhaseRequirements(phase);
  }

  async detectCurrentPhase(): Promise<string> {
    // Logic to detect current phase based on existing artifacts
    const phases = Object.keys(this.config.phases);
    
    for (let i = phases.length - 1; i >= 0; i--) {
      const phase = this.config.phases[phases[i]];
      const hasArtifacts = await this.phaseValidator.hasRequiredArtifacts(phase);
      if (hasArtifacts) {
        return phases[i];
      }
    }
    
    return phases[0]; // Default to first phase
  }

  getNextPhase(currentPhase: string): string | null {
    const phases = Object.keys(this.config.phases);
    const currentIndex = phases.indexOf(currentPhase);
    return currentIndex < phases.length - 1 ? phases[currentIndex + 1] : null;
  }

  displayResults(details: Array<{ check: string; passed: boolean; message?: string }>): void {
    details.forEach(detail => {
      const icon = detail.passed ? '✅' : '❌';
      const color = detail.passed ? chalk.green : chalk.red;
      console.log(color(`  ${icon} ${detail.check}`));
      if (detail.message) {
        console.log(color(`     ${detail.message}`));
      }
    });
  }

  displayPhaseRequirements(phase: Phase): void {
    console.log(chalk.cyan(`\n📋 Phase Requirements:`));
    console.log(chalk.cyan(`   ${phase.description}`));
    
    if (phase.required_artifacts) {
      console.log(chalk.cyan(`\n📁 Required Artifacts:`));
      phase.required_artifacts.forEach(artifact => {
        console.log(chalk.cyan(`   • ${artifact}`));
      });
    }

    if (phase.validation) {
      console.log(chalk.cyan(`\n🔍 Validations:`));
      phase.validation.forEach(validation => {
        console.log(chalk.cyan(`   • ${validation}`));
      });
    }
  }
}

// CLI Command definitions
program
  .name('ae-framework')
  .description('AI-Agent Enabled Framework CLI')
  .version('1.0.0');

program
  .command('check')
  .description('Validate current phase requirements')
  .option('-p, --phase <phase>', 'Specific phase to check')
  .action(async (options) => {
    const cli = new AEFrameworkCLI();
    
    if (options.phase) {
      await cli.checkPhase(options.phase);
    } else {
      const currentPhase = await cli.detectCurrentPhase();
      await cli.checkPhase(currentPhase);
    }
  });

program
  .command('guard')
  .description('Run guard validations')
  .option('-n, --name <name>', 'Specific guard to run')
  .action(async (options) => {
    const cli = new AEFrameworkCLI();
    await cli.runGuards(options.name);
  });

program
  .command('next')
  .description('Move to next phase with validation')
  .action(async () => {
    const cli = new AEFrameworkCLI();
    await cli.nextPhase();
  });

program
  .command('tdd')
  .description('Run TDD cycle validation')
  .action(async () => {
    const cli = new AEFrameworkCLI();
    console.log(chalk.blue('🔄 Validating TDD cycle...'));
    
    // Check TDD Guards
    await cli.runGuards('TDD Guard');
    await cli.runGuards('Test Execution Guard');
    await cli.runGuards('RED-GREEN Cycle Guard');
    
    console.log(chalk.green('✅ TDD cycle validation complete'));
  });

program.parse();

export { AEFrameworkCLI };