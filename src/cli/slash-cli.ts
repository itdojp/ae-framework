#!/usr/bin/env node

/**
 * Interactive slash command CLI for ae-framework
 */

import { Command } from 'commander';
import { SlashCommandManager } from '../commands/slash-command-manager.js';
import chalk from 'chalk';
import { toMessage } from '../utils/error-utils.js';
import { safeExit } from '../utils/safe-exit.js';
import * as readline from 'readline';

const program = new Command();

program
  .name('ae-slash')
  .description('Interactive slash command interface for ae-framework')
  .version('1.0.0');

// Execute single command
program
  .command('exec <command>')
  .description('Execute a single slash command')
  .action(async (command: string) => {
    const manager = new SlashCommandManager();
    
    try {
      const result = await manager.execute(command);
      
      if (result.success) {
        console.log(chalk.green('✅ Success'));
        console.log(result.message);
        
        if (result.data) {
          console.log(chalk.gray('\nData:'));
          console.log(JSON.stringify(result.data, null, 2));
        }
        
        if (result.nextCommand) {
          console.log(chalk.yellow(`\n💡 Suggested next: ${result.nextCommand}`));
        }
      } else {
        console.log(chalk.red('❌ Failed'));
        console.log(result.message);
      }
  } catch (error: unknown) {
    console.error(chalk.red(`❌ Error: ${toMessage(error)}`));
    safeExit(1);
  }
  });

// Parse commands from text
program
  .command('parse <text>')
  .description('Extract slash commands from text')
  .action((text: string) => {
    const manager = new SlashCommandManager();
    const commands = manager.parseCommandFromText(text);
    
    if (commands.length === 0) {
      console.log(chalk.gray('No commands found in text'));
    } else {
      console.log(chalk.blue(`Found ${commands.length} command(s):`));
      commands.forEach((cmd, i) => {
        console.log(`  ${i + 1}. ${cmd}`);
      });
    }
  });

// Execute command sequence
program
  .command('sequence <commands...>')
  .description('Execute multiple commands in sequence')
  .action(async (commands: string[]) => {
    const manager = new SlashCommandManager();
    
    try {
      console.log(chalk.blue(`Executing ${commands.length} commands...\n`));
      
      const results = await manager.executeSequence(commands);
      
      results.forEach((result, i) => {
        const commandIndex = i < commands.length ? i : commands.length - 1;
        console.log(chalk.bold(`\n[${i + 1}] ${commands[commandIndex] || 'Suggested command'}:`));
        
        if (result.success) {
          console.log(chalk.green('✅ Success'));
        } else {
          console.log(chalk.red('❌ Failed'));
        }
        
        console.log(result.message);
      });
      
      const successCount = results.filter(r => r.success).length;
      console.log(chalk.blue(`\n📊 Results: ${successCount}/${results.length} successful`));
  } catch (error: unknown) {
    console.error(chalk.red(`❌ Error: ${toMessage(error)}`));
    safeExit(1);
  }
  });

// List all commands
program
  .command('list')
  .description('List all available slash commands')
  .option('-c, --category <category>', 'Filter by category')
  .action((options) => {
    const manager = new SlashCommandManager();
    const commands = manager.getCommands();
    
    const categories = ['phase', 'workflow', 'info', 'utility'];
    const filterCategory = options.category;
    
    if (filterCategory && !categories.includes(filterCategory)) {
      console.log(chalk.red(`Invalid category. Valid categories: ${categories.join(', ')}`));
      return;
    }
    
    console.log(chalk.bold('\nAvailable Slash Commands:\n'));
    
    for (const category of categories) {
      if (filterCategory && category !== filterCategory) continue;
      
      const categoryCommands = commands.filter(c => c.category === category);
      if (categoryCommands.length === 0) continue;
      
      console.log(chalk.yellow(`${category.toUpperCase()} COMMANDS:`));
      
      for (const cmd of categoryCommands) {
        console.log(`  ${chalk.cyan(cmd.name.padEnd(15))} - ${cmd.description}`);
        if (cmd.aliases && cmd.aliases.length > 0) {
          console.log(chalk.gray(`${''.padEnd(17)}Aliases: ${cmd.aliases.join(', ')}`));
        }
      }
      console.log('');
    }
  });

// Interactive mode
program
  .command('interactive')
  .alias('i')
  .description('Start interactive slash command mode')
  .action(async () => {
    const manager = new SlashCommandManager();
    const rl = readline.createInterface({
      input: process.stdin,
      output: process.stdout,
      prompt: chalk.cyan('ae> '),
    });
    
    console.log(chalk.bold('\n🚀 ae-framework Interactive Slash Command Mode'));
    console.log(chalk.gray('Type /help for available commands, /exit to quit\n'));
    
    // Show initial status
    const statusResult = await manager.execute('/status');
    if (statusResult.success) {
      console.log(statusResult.message);
    } else {
      console.log(chalk.yellow('No project found. Use /init to create one.'));
    }
    console.log('');
    
    rl.prompt();
    
    rl.on('line', async (line) => {
      const input = line.trim();
      
      if (input === '/exit' || input === '/quit') {
        console.log(chalk.gray('\nGoodbye!'));
        rl.close();
        return;
      }
      
      if (input === '') {
        rl.prompt();
        return;
      }
      
      try {
        // Check if input contains slash commands
        const commands = input.startsWith('/') 
          ? [input] 
          : manager.parseCommandFromText(input);
        
        if (commands.length === 0) {
          console.log(chalk.gray('No command detected. Start with / for commands.'));
        } else {
          for (const command of commands) {
            const result = await manager.execute(command);
            
            if (result.success) {
              console.log(chalk.green('✅'), result.message);
              
              if (result.nextCommand) {
                console.log(chalk.yellow(`💡 Suggested: ${result.nextCommand}`));
              }
            } else {
              console.log(chalk.red('❌'), result.message);
            }
          }
        }
    } catch (error: unknown) {
      console.error(chalk.red(`❌ Error: ${toMessage(error)}`));
    }
      
      console.log('');
      rl.prompt();
    });
    
    rl.on('close', () => {
      safeExit(0);
    });
  });

// Help command
program
  .command('help [command]')
  .description('Show help for a specific slash command')
  .action(async (command?: string) => {
    const manager = new SlashCommandManager();
    
    if (command) {
      const result = await manager.execute(`/help ${command}`);
      console.log(result.message);
    } else {
      const result = await manager.execute('/help');
      console.log(result.message);
    }
  });

// Default action - show help
if (process.argv.length === 2) {
  program.outputHelp();
  console.log(chalk.gray('\nTip: Use "ae-slash interactive" to start interactive mode'));
} else {
  program.parse();
}
