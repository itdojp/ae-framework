#!/usr/bin/env node

/**
 * CLI for managing ae-framework phase state
 */

import { Command } from 'commander';
import { PhaseStateManager } from '../utils/phase-state-manager.js';
import type { PhaseType } from '../utils/phase-state-manager.js';
import * as fs from 'fs';
import * as path from 'path';
import { toMessage } from '../utils/error-utils.js';
import { safeExit } from '../utils/safe-exit.js';
import chalk from 'chalk';

const program = new Command();
const manager = new PhaseStateManager();

program
  .name('ae-phase')
  .description('CLI for managing ae-framework project phases')
  .version('1.0.0');

// Initialize project
program
  .command('init')
  .description('Initialize a new ae-framework project')
  .option('-n, --name <name>', 'Project name')
  .option('--no-approvals', 'Disable approval requirements')
  .action(async (options) => {
    try {
      const hasProject = await manager.hasProject();
      if (hasProject) {
        console.error(chalk.red('❌ Project already initialized. Use "ae-phase reset" to start over.'));
        safeExit(1);
      }

      const state = await manager.initializeProject(
        options.name,
        options.approvals !== false
      );

      console.log('✅ Project initialized successfully!');
      console.log(`📋 Project ID: ${state.projectId}`);
      if (state.projectName) {
        console.log(`📝 Project Name: ${state.projectName}`);
      }
      console.log(`🔒 Approvals Required: ${state.approvalsRequired ? 'Yes' : 'No'}`);
      console.log(`📍 Current Phase: ${state.currentPhase}`);
    } catch (error: unknown) {
      console.error(chalk.red(`❌ Error: ${toMessage(error)}`));
      safeExit(1);
    }
  });

// Show status
program
  .command('status')
  .description('Show current project status')
  .option('-v, --verbose', 'Show detailed status')
  .action(async (options) => {
    try {
      const state = await manager.getCurrentState();
      if (!state) {
        console.error(chalk.red('❌ No project found. Run "ae-phase init" first.'));
        safeExit(1);
      }

      if (options.verbose) {
        const report = await manager.generateStatusReport();
        console.log(report);
      } else {
        const progress = await manager.getProgressPercentage();
        console.log(`📊 Project: ${state.projectName || state.projectId}`);
        console.log(`📍 Current Phase: ${state.currentPhase}`);
        console.log(`📈 Progress: ${progress}%`);
        
        const currentStatus = state.phaseStatus[state.currentPhase];
        if (currentStatus.completed) {
          if (currentStatus.approved) {
            console.log(`✅ Current phase is completed and approved`);
          } else if (state.approvalsRequired) {
            console.log(`⏳ Current phase is completed, awaiting approval`);
          } else {
            console.log(`✅ Current phase is completed`);
          }
        } else if (currentStatus.startedAt) {
          console.log(`🚀 Current phase is in progress`);
        } else {
          console.log(`📝 Current phase not started`);
        }
      }
    } catch (error: unknown) {
      console.error(chalk.red(`❌ Error: ${toMessage(error)}`));
      safeExit(1);
    }
  });

// Start phase
program
  .command('start <phase>')
  .description('Start a phase')
  .action(async (phase: PhaseType) => {
    try {
      await manager.startPhase(phase);
      console.log(`✅ Started phase: ${phase}`);
    } catch (error: unknown) {
      console.error(chalk.red(`❌ Error: ${toMessage(error)}`));
      safeExit(1);
    }
  });

// Complete phase
program
  .command('complete <phase>')
  .description('Mark a phase as completed')
  .option('-a, --artifacts <artifacts...>', 'List of artifact files')
  .action(async (phase: PhaseType, options) => {
    try {
      const artifacts = options.artifacts || [];
      await manager.completePhase(phase, artifacts);
      console.log(`✅ Completed phase: ${phase}`);
      
      if (artifacts.length > 0) {
        console.log(`📦 Artifacts recorded:`);
        artifacts.forEach((a: string) => console.log(`   - ${a}`));
      }

      const state = await manager.getCurrentState();
      if (state?.approvalsRequired) {
        console.log(`⏳ Phase requires approval before proceeding`);
      }
    } catch (error: unknown) {
      console.error(chalk.red(`❌ Error: ${toMessage(error)}`));
      safeExit(1);
    }
  });

// Approve phase
program
  .command('approve <phase>')
  .description('Approve a completed phase')
  .option('-u, --user <user>', 'Approver name', 'CLI User')
  .option('-n, --notes <notes>', 'Approval notes')
  .action(async (phase: PhaseType, options) => {
    try {
      await manager.approvePhase(phase, options.user, options.notes);
      console.log(`✅ Approved phase: ${phase}`);
      console.log(`👤 Approved by: ${options.user}`);
      
      if (options.notes) {
        console.log(`📝 Notes: ${options.notes}`);
      }

      // Check if can transition to next phase
      const canTransition = await manager.canTransitionToNextPhase();
      if (canTransition) {
        const state = await manager.getCurrentState();
        const nextPhase = manager.getNextPhase(state!.currentPhase);
        console.log(`➡️  Ready to transition to phase: ${nextPhase}`);
      }
    } catch (error: unknown) {
      console.error(chalk.red(`❌ Error: ${toMessage(error)}`));
      safeExit(1);
    }
  });

// Transition to next phase
program
  .command('next')
  .description('Transition to the next phase')
  .action(async () => {
    try {
      const nextPhase = await manager.transitionToNextPhase();
      if (nextPhase) {
        console.log(`✅ Transitioned to phase: ${nextPhase}`);
      } else {
        console.log(`🎉 All phases completed!`);
      }
    } catch (error: unknown) {
      console.error(chalk.red(`❌ Error: ${toMessage(error)}`));
      safeExit(1);
    }
  });

// Show timeline
program
  .command('timeline')
  .description('Show phase timeline')
  .action(async () => {
    try {
      const timeline = await manager.getPhaseTimeline();
      
      console.log('\n📅 Phase Timeline\n');
      console.log('Phase    | Status       | Started    | Completed  | Duration');
      console.log('---------|--------------|------------|------------|----------');
      
      for (const item of timeline) {
        const phase = item.phase.padEnd(8);
        const status = item.status.padEnd(12);
        const started = item.startedAt ? 
          item.startedAt.toISOString().split('T')[0] : 
          '---       ';
        const completed = item.completedAt ? 
          item.completedAt.toISOString().split('T')[0] : 
          '---       ';
        const duration = item.duration ? 
          `${Math.round(item.duration / 1000 / 60)} min` : 
          '---';
        
        console.log(`${phase} | ${status} | ${started} | ${completed} | ${duration}`);
      }
    } catch (error: unknown) {
      console.error(chalk.red(`❌ Error: ${toMessage(error)}`));
      process.exit(1);
    }
  });

// Reset phase
program
  .command('reset [phase]')
  .description('Reset a phase or entire project')
  .option('-f, --force', 'Force reset without confirmation')
  .action(async (phase: PhaseType | undefined, options) => {
    try {
      if (!options.force) {
        console.log('⚠️  This will reset phase data. Use --force to confirm.');
        safeExit(1);
      }

      if (phase) {
        await manager.resetPhase(phase);
        console.log(`✅ Reset phase: ${phase}`);
      } else {
        // Reset entire project
        const stateFile = path.join(process.cwd(), '.ae', 'phase-state.json');
        try {
          await fs.promises.unlink(stateFile);
          console.log(`✅ Reset entire project`);
        } catch (error: unknown) {
          // File might not exist, which is fine
          console.log(`✅ Project reset (no existing state found)`);
        }
      }
    } catch (error: unknown) {
      console.error(chalk.red(`❌ Error: ${toMessage(error)}`));
      safeExit(1);
    }
  });

// Show artifacts
program
  .command('artifacts <phase>')
  .description('Show artifacts for a phase')
  .action(async (phase: PhaseType) => {
    try {
      const artifacts = await manager.getPhaseArtifacts(phase);
      
      if (artifacts.length === 0) {
        console.log(`📦 No artifacts found for phase: ${phase}`);
      } else {
        console.log(`📦 Artifacts for phase ${phase}:`);
        artifacts.forEach(a => console.log(`   - ${a}`));
      }
    } catch (error: unknown) {
      console.error(chalk.red(`❌ Error: ${toMessage(error)}`));
      safeExit(1);
    }
  });

program.parse();
