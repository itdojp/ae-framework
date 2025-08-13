#!/usr/bin/env node

/**
 * CLI for managing approval workflows in ae-framework
 */

import { Command } from 'commander';
import { ApprovalService } from '../services/approval-service.js';
import { PhaseType } from '../utils/phase-state-manager.js';
import chalk from 'chalk';

const program = new Command();
const service = new ApprovalService();

program
  .name('ae-approve')
  .description('CLI for managing ae-framework approval workflows')
  .version('1.0.0');

// Request approval
program
  .command('request <phase>')
  .description('Request approval for a completed phase')
  .option('-u, --user <user>', 'Requester name', 'User')
  .option('-s, --summary <summary>', 'Summary of changes')
  .action(async (phase: PhaseType, options) => {
    try {
      const request = await service.requestApproval(
        phase,
        options.user,
        options.summary
      );

      console.log(chalk.green('✅ Approval requested successfully!'));
      console.log(chalk.blue(`📋 Phase: ${phase}`));
      console.log(chalk.blue(`👤 Requested by: ${options.user}`));
      
      if (request.artifacts.length > 0) {
        console.log(chalk.blue(`📦 Artifacts:`));
        request.artifacts.forEach(a => console.log(chalk.gray(`   - ${a}`)));
      }

      // Check if auto-approved
      const status = await service.getApprovalStatus(phase);
      if (status.status === 'approved') {
        console.log(chalk.green('🎉 Phase was auto-approved!'));
      } else {
        console.log(chalk.yellow('⏳ Waiting for approval...'));
      }
    } catch (error: any) {
      console.error(chalk.red(`❌ Error: ${error.message}`));
      process.exit(1);
    }
  });

// Approve phase
program
  .command('approve <phase>')
  .description('Approve a phase')
  .option('-u, --user <user>', 'Approver name', 'Approver')
  .option('-n, --notes <notes>', 'Approval notes')
  .option('-c, --conditions <conditions...>', 'Approval conditions')
  .action(async (phase: PhaseType, options) => {
    try {
      await service.approve(
        phase,
        options.user,
        options.notes,
        options.conditions
      );

      console.log(chalk.green(`✅ Phase ${phase} approved!`));
      console.log(chalk.blue(`👤 Approved by: ${options.user}`));
      
      if (options.notes) {
        console.log(chalk.blue(`📝 Notes: ${options.notes}`));
      }
      
      if (options.conditions?.length > 0) {
        console.log(chalk.blue(`📋 Conditions:`));
        options.conditions.forEach((c: string) => console.log(chalk.gray(`   - ${c}`)));
      }
    } catch (error: any) {
      console.error(chalk.red(`❌ Error: ${error.message}`));
      process.exit(1);
    }
  });

// Reject approval
program
  .command('reject <phase>')
  .description('Reject an approval request')
  .option('-u, --user <user>', 'Reviewer name', 'Reviewer')
  .requiredOption('-r, --reason <reason>', 'Rejection reason')
  .action(async (phase: PhaseType, options) => {
    try {
      await service.reject(phase, options.user, options.reason);

      console.log(chalk.red(`❌ Phase ${phase} approval rejected`));
      console.log(chalk.blue(`👤 Rejected by: ${options.user}`));
      console.log(chalk.blue(`📝 Reason: ${options.reason}`));
    } catch (error: any) {
      console.error(chalk.red(`❌ Error: ${error.message}`));
      process.exit(1);
    }
  });

// List pending approvals
program
  .command('pending')
  .description('List all pending approvals')
  .action(async () => {
    try {
      const pending = await service.getPendingApprovals();
      
      if (pending.length === 0) {
        console.log(chalk.green('✅ No pending approvals'));
        return;
      }

      console.log(chalk.yellow(`\n📋 Pending Approvals (${pending.length})\n`));
      
      for (const approval of pending) {
        const { request, policy, responses } = approval;
        
        console.log(chalk.bold(`Phase: ${request.phase}`));
        console.log(`  Requested by: ${request.requestedBy}`);
        console.log(`  Requested at: ${request.requestedAt.toISOString()}`);
        
        if (request.summary) {
          console.log(`  Summary: ${request.summary}`);
        }
        
        if (request.artifacts.length > 0) {
          console.log(`  Artifacts: ${request.artifacts.join(', ')}`);
        }
        
        if (policy.requireMultipleApprovers) {
          const approved = responses.filter(r => r.approved).length;
          const required = policy.minApprovers || 1;
          console.log(`  Approvals: ${approved}/${required}`);
        }
        
        if (approval.expiresAt) {
          const hoursLeft = Math.round(
            (approval.expiresAt.getTime() - Date.now()) / (1000 * 60 * 60)
          );
          if (hoursLeft > 0) {
            console.log(chalk.yellow(`  Expires in: ${hoursLeft} hours`));
          } else {
            console.log(chalk.red(`  Expired`));
          }
        }
        
        console.log('');
      }
    } catch (error: any) {
      console.error(chalk.red(`❌ Error: ${error.message}`));
      process.exit(1);
    }
  });

// Show approval status
program
  .command('status <phase>')
  .description('Show approval status for a phase')
  .action(async (phase: PhaseType) => {
    try {
      const status = await service.getApprovalStatus(phase);
      
      console.log(chalk.bold(`\nApproval Status for ${phase}\n`));
      
      if (!status.required) {
        console.log(chalk.green('✅ Approvals not required for this project'));
        return;
      }

      switch (status.status) {
        case 'approved':
          console.log(chalk.green('✅ Approved'));
          break;
        case 'pending':
          console.log(chalk.yellow('⏳ Pending approval'));
          break;
        case 'rejected':
          console.log(chalk.red('❌ Rejected'));
          break;
        case 'expired':
          console.log(chalk.red('⏰ Expired'));
          break;
        default:
          console.log(chalk.gray('📝 Not yet requested'));
      }

      if (status.details) {
        const { request, policy, responses } = status.details;
        
        console.log(`\nRequested by: ${request.requestedBy}`);
        console.log(`Requested at: ${request.requestedAt.toISOString()}`);
        
        if (policy.requireMultipleApprovers) {
          const approved = responses.filter(r => r.approved).length;
          const required = policy.minApprovers || 1;
          console.log(`Approvals: ${approved}/${required} required`);
          
          if (responses.length > 0) {
            console.log('\nResponses:');
            for (const response of responses) {
              const icon = response.approved ? '✅' : '❌';
              console.log(`  ${icon} ${response.approvedBy} - ${response.notes || 'No notes'}`);
            }
          }
        }
      }
    } catch (error: any) {
      console.error(chalk.red(`❌ Error: ${error.message}`));
      process.exit(1);
    }
  });

// Show approval history
program
  .command('history <phase>')
  .description('Show approval history for a phase')
  .action(async (phase: PhaseType) => {
    try {
      const history = await service.getApprovalHistory(phase);
      
      if (history.length === 0) {
        console.log(chalk.gray(`No approval history for phase ${phase}`));
        return;
      }

      console.log(chalk.bold(`\nApproval History for ${phase}\n`));
      
      for (const item of history) {
        const statusColor = item.status === 'approved' ? chalk.green :
                          item.status === 'rejected' ? chalk.red :
                          chalk.yellow;
        
        console.log(statusColor(`[${item.status.toUpperCase()}]`));
        console.log(`  Requested by: ${item.request.requestedBy}`);
        console.log(`  Date: ${item.createdAt}`);
        
        if (item.responses.length > 0) {
          console.log(`  Responses:`);
          for (const response of item.responses) {
            const icon = response.approved ? '✅' : '❌';
            console.log(`    ${icon} ${response.approvedBy}: ${response.notes || 'No notes'}`);
          }
        }
        console.log('');
      }
    } catch (error: any) {
      console.error(chalk.red(`❌ Error: ${error.message}`));
      process.exit(1);
    }
  });

// Check expired approvals
program
  .command('check-expired')
  .description('Check and clean up expired approval requests')
  .action(async () => {
    try {
      await service.checkExpiredApprovals();
      console.log(chalk.green('✅ Checked for expired approvals'));
    } catch (error: any) {
      console.error(chalk.red(`❌ Error: ${error.message}`));
      process.exit(1);
    }
  });

// Set policy
program
  .command('set-policy <phase>')
  .description('Configure approval policy for a phase')
  .option('-m, --multiple', 'Require multiple approvers')
  .option('-n, --min-approvers <number>', 'Minimum number of approvers', parseInt)
  .option('-t, --timeout <hours>', 'Approval timeout in hours', parseInt)
  .option('--auto-test', 'Enable auto-approval with test coverage')
  .option('--auto-security', 'Enable auto-approval with security scan')
  .action(async (phase: PhaseType, options) => {
    try {
      const policy: any = {};
      
      if (options.multiple !== undefined) {
        policy.requireMultipleApprovers = options.multiple;
      }
      
      if (options.minApprovers !== undefined) {
        policy.minApprovers = options.minApprovers;
      }
      
      if (options.timeout !== undefined) {
        policy.timeoutHours = options.timeout;
      }
      
      if (options.autoTest || options.autoSecurity) {
        policy.autoApproveConditions = [];
        
        if (options.autoTest) {
          policy.autoApproveConditions.push({
            type: 'test-coverage',
            threshold: 80
          });
        }
        
        if (options.autoSecurity) {
          policy.autoApproveConditions.push({
            type: 'security-scan'
          });
        }
      }
      
      service.setPolicy(phase, policy);
      
      console.log(chalk.green(`✅ Updated approval policy for phase ${phase}`));
      console.log(chalk.blue('Policy settings:'));
      console.log(JSON.stringify(policy, null, 2));
    } catch (error: any) {
      console.error(chalk.red(`❌ Error: ${error.message}`));
      process.exit(1);
    }
  });

program.parse();