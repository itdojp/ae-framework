/**
 * Slash Command Manager for ae-framework
 * Provides a unified interface for executing commands across all agents
 */

import { IntentAgent } from '../agents/intent-agent.js';
import { FormalAgent } from '../agents/formal-agent.js';
import { TestGenerationAgent } from '../agents/test-generation-agent.js';
import { CodeGenerationAgent } from '../agents/code-generation-agent.js';
import { VerifyAgent } from '../agents/verify-agent.js';
import { OperateAgent } from '../agents/operate-agent.js';
import { PhaseStateManager, PhaseType } from '../utils/phase-state-manager.js';
import { SteeringLoader } from '../utils/steering-loader.js';
import { ApprovalService } from '../services/approval-service.js';
import { 
  AnalyzeCommand,
  TroubleshootCommand,
  ImproveCommand,
  DocumentCommand
} from './extended/index.js';

export interface SlashCommand {
  name: string;
  description: string;
  category: 'phase' | 'utility' | 'info' | 'workflow';
  usage: string;
  aliases?: string[];
  handler: CommandHandler;
  requiresPhase?: PhaseType;
  stopOnFailure?: boolean; // Whether to stop sequence execution on failure (default: true)
}

export type CommandHandler = (args: string[], context: CommandContext) => Promise<CommandResult>;

export interface CommandContext {
  phaseStateManager: PhaseStateManager;
  steeringLoader: SteeringLoader;
  approvalService: ApprovalService;
  currentPhase?: PhaseType;
  projectRoot: string;
}

export interface CommandResult {
  success: boolean;
  message?: string;
  data?: any;
  nextCommand?: string;
}

export class SlashCommandManager {
  private commands: Map<string, SlashCommand> = new Map();
  private aliases: Map<string, string> = new Map();
  private context: CommandContext;
  
  // Lazy-loaded agent instances
  private intentAgent?: IntentAgent;
  private formalAgent?: FormalAgent;
  private testAgent?: TestGenerationAgent;
  private codeAgent?: CodeGenerationAgent;
  private verifyAgent?: VerifyAgent;
  private operateAgent?: OperateAgent;

  constructor(projectRoot?: string) {
    const root = projectRoot || process.cwd();
    
    // Initialize context
    const phaseStateManager = new PhaseStateManager(root);
    this.context = {
      phaseStateManager,
      steeringLoader: new SteeringLoader(root),
      approvalService: new ApprovalService(root, phaseStateManager),
      projectRoot: root,
    };

    // Register commands (agents will be initialized on demand)
    this.registerCommands();
    this.registerExtendedCommands();
  }

  /**
   * Get or create intent agent
   */
  private getIntentAgent(): IntentAgent {
    if (!this.intentAgent) {
      this.intentAgent = new IntentAgent();
    }
    return this.intentAgent;
  }

  /**
   * Get or create formal agent
   */
  private getFormalAgent(): FormalAgent {
    if (!this.formalAgent) {
      this.formalAgent = new FormalAgent();
    }
    return this.formalAgent;
  }

  /**
   * Get or create test agent
   */
  private getTestAgent(): TestGenerationAgent {
    if (!this.testAgent) {
      this.testAgent = new TestGenerationAgent();
    }
    return this.testAgent;
  }

  /**
   * Get or create code agent
   */
  private getCodeAgent(): CodeGenerationAgent {
    if (!this.codeAgent) {
      this.codeAgent = new CodeGenerationAgent();
    }
    return this.codeAgent;
  }

  /**
   * Get or create verify agent
   */
  private getVerifyAgent(): VerifyAgent {
    if (!this.verifyAgent) {
      this.verifyAgent = new VerifyAgent();
    }
    return this.verifyAgent;
  }

  /**
   * Get or create operate agent
   */
  private getOperateAgent(): OperateAgent {
    if (!this.operateAgent) {
      this.operateAgent = new OperateAgent();
    }
    return this.operateAgent;
  }

  /**
   * Register extended commands from Issue #17
   */
  private registerExtendedCommands(): void {
    // Register analyze command
    const analyzeCmd = new AnalyzeCommand();
    this.registerCommand({
      name: analyzeCmd.name,
      description: analyzeCmd.description,
      category: analyzeCmd.category,
      usage: analyzeCmd.usage,
      aliases: analyzeCmd.aliases,
      handler: analyzeCmd.handler.bind(analyzeCmd),
      stopOnFailure: false
    });

    // Register troubleshoot command
    const troubleshootCmd = new TroubleshootCommand();
    this.registerCommand({
      name: troubleshootCmd.name,
      description: troubleshootCmd.description,
      category: troubleshootCmd.category,
      usage: troubleshootCmd.usage,
      aliases: troubleshootCmd.aliases,
      handler: troubleshootCmd.handler.bind(troubleshootCmd)
    });

    // Register improve command
    const improveCmd = new ImproveCommand();
    this.registerCommand({
      name: improveCmd.name,
      description: improveCmd.description,
      category: improveCmd.category,
      usage: improveCmd.usage,
      aliases: improveCmd.aliases,
      handler: improveCmd.handler.bind(improveCmd)
    });

    // Register document command
    const documentCmd = new DocumentCommand();
    this.registerCommand({
      name: documentCmd.name,
      description: documentCmd.description,
      category: documentCmd.category,
      usage: documentCmd.usage,
      aliases: documentCmd.aliases,
      handler: documentCmd.handler.bind(documentCmd),
      stopOnFailure: false
    });
  }

  /**
   * Register all available commands
   */
  private registerCommands(): void {
    // Phase commands
    this.registerCommand({
      name: '/intent',
      description: 'Analyze requirements and extract intent',
      category: 'phase',
      usage: '/intent <requirement text>',
      aliases: ['/i', '/requirements'],
      requiresPhase: 'intent',
      handler: this.handleIntentCommand.bind(this),
    });

    this.registerCommand({
      name: '/formal',
      description: 'Generate formal specifications',
      category: 'phase',
      usage: '/formal <spec type> [options]',
      aliases: ['/f', '/spec'],
      requiresPhase: 'formal',
      handler: this.handleFormalCommand.bind(this),
    });

    this.registerCommand({
      name: '/test',
      description: 'Generate tests for specifications',
      category: 'phase',
      usage: '/test <file> [test type]',
      aliases: ['/t', '/generate-tests'],
      requiresPhase: 'test',
      handler: this.handleTestCommand.bind(this),
    });

    this.registerCommand({
      name: '/code',
      description: 'Generate code from tests',
      category: 'phase',
      usage: '/code <test file>',
      aliases: ['/c', '/implement'],
      requiresPhase: 'code',
      handler: this.handleCodeCommand.bind(this),
    });

    this.registerCommand({
      name: '/verify',
      description: 'Verify implementation',
      category: 'phase',
      usage: '/verify [options]',
      aliases: ['/v', '/check'],
      requiresPhase: 'verify',
      handler: this.handleVerifyCommand.bind(this),
    });

    this.registerCommand({
      name: '/operate',
      description: 'Deploy and monitor application',
      category: 'phase',
      usage: '/operate <action>',
      aliases: ['/o', '/deploy'],
      requiresPhase: 'operate',
      handler: this.handleOperateCommand.bind(this),
    });

    // Workflow commands
    this.registerCommand({
      name: '/init',
      description: 'Initialize a new ae-framework project',
      category: 'workflow',
      usage: '/init [project name]',
      handler: this.handleInitCommand.bind(this),
    });

    this.registerCommand({
      name: '/status',
      description: 'Show current project status',
      category: 'info',
      usage: '/status',
      aliases: ['/s'],
      handler: this.handleStatusCommand.bind(this),
      stopOnFailure: false, // Status command doesn't stop sequence execution
    });

    this.registerCommand({
      name: '/next',
      description: 'Move to the next phase',
      category: 'workflow',
      usage: '/next',
      aliases: ['/n'],
      handler: this.handleNextCommand.bind(this),
    });

    this.registerCommand({
      name: '/approve',
      description: 'Approve current phase',
      category: 'workflow',
      usage: '/approve [notes]',
      aliases: ['/a'],
      handler: this.handleApproveCommand.bind(this),
    });

    this.registerCommand({
      name: '/complete',
      description: 'Mark current phase as complete',
      category: 'workflow',
      usage: '/complete [artifacts...]',
      handler: this.handleCompleteCommand.bind(this),
    });

    // Utility commands
    this.registerCommand({
      name: '/help',
      description: 'Show help for commands',
      category: 'utility',
      usage: '/help [command]',
      aliases: ['/h', '/?'],
      handler: this.handleHelpCommand.bind(this),
      stopOnFailure: false, // Help commands don't stop sequence execution
    });

    this.registerCommand({
      name: '/steering',
      description: 'Manage steering documents',
      category: 'utility',
      usage: '/steering <action> [document]',
      handler: this.handleSteeringCommand.bind(this),
    });

    this.registerCommand({
      name: '/context',
      description: 'Show current context',
      category: 'info',
      usage: '/context',
      aliases: ['/ctx'],
      handler: this.handleContextCommand.bind(this),
      stopOnFailure: false, // Context command doesn't stop sequence execution
    });

    this.registerCommand({
      name: '/timeline',
      description: 'Show phase timeline',
      category: 'info',
      usage: '/timeline',
      aliases: ['/tl'],
      handler: this.handleTimelineCommand.bind(this),
      stopOnFailure: false, // Timeline command doesn't stop sequence execution
    });

    this.registerCommand({
      name: '/run',
      description: 'Run a specific phase workflow',
      category: 'workflow',
      usage: '/run <phase> [options]',
      handler: this.handleRunCommand.bind(this),
    });
  }

  /**
   * Register a command
   */
  private registerCommand(command: SlashCommand): void {
    this.commands.set(command.name, command);
    
    // Register aliases
    if (command.aliases) {
      for (const alias of command.aliases) {
        this.aliases.set(alias, command.name);
      }
    }
  }

  /**
   * Execute a command
   */
  async execute(input: string): Promise<CommandResult> {
    const parts = input.trim().split(/\s+/);
    const commandName = parts[0];
    const args = parts.slice(1);

    // Resolve alias if needed
    const resolvedName = this.aliases.get(commandName) || commandName;
    
    // Find command
    const command = this.commands.get(resolvedName);
    if (!command) {
      return {
        success: false,
        message: `Unknown command: ${commandName}. Use /help to see available commands.`,
      };
    }

    // Update current phase in context
    const state = await this.context.phaseStateManager.getCurrentState();
    if (state) {
      this.context.currentPhase = state.currentPhase;
    }

    // Check phase requirement
    if (command.requiresPhase && this.context.currentPhase !== command.requiresPhase) {
      return {
        success: false,
        message: `Command ${commandName} requires phase ${command.requiresPhase}, but current phase is ${this.context.currentPhase}`,
      };
    }

    try {
      return await command.handler(args, this.context);
    } catch (error: any) {
      return {
        success: false,
        message: `Error executing command: ${error.message}`,
      };
    }
  }

  // Command Handlers

  private async handleIntentCommand(args: string[], context: CommandContext): Promise<CommandResult> {
    if (args.length === 0) {
      return {
        success: false,
        message: 'Please provide requirement text',
      };
    }

    const requirementText = args.join(' ');
    const requirements = await this.getIntentAgent().extractFromNaturalLanguage(requirementText);
    
    return {
      success: true,
      message: `Extracted ${requirements.length} requirements`,
      data: requirements,
    };
  }

  private async handleFormalCommand(args: string[], context: CommandContext): Promise<CommandResult> {
    if (args.length === 0) {
      return {
        success: false,
        message: 'Please specify specification type (openapi, asyncapi, graphql, tla)',
      };
    }

    const specType = args[0];
    const previousArtifacts = await context.phaseStateManager.getPhaseArtifacts('intent');
    
    // Generate formal specification based on type
    let result: any;
    switch (specType) {
      case 'openapi':
        result = await this.getFormalAgent().generateOpenAPISpec({
          title: 'Generated API',
          version: '1.0.0',
          sourceFiles: previousArtifacts,
        });
        break;
      case 'tla':
        result = await this.getFormalAgent().generateTLAPlus({
          moduleName: 'System',
          requirements: previousArtifacts,
        });
        break;
      default:
        return {
          success: false,
          message: `Unknown specification type: ${specType}`,
        };
    }

    return {
      success: true,
      message: `Generated ${specType} specification`,
      data: result,
    };
  }

  private async handleTestCommand(args: string[], context: CommandContext): Promise<CommandResult> {
    if (args.length === 0) {
      return {
        success: false,
        message: 'Please specify a file to generate tests for',
      };
    }

    const filePath = args[0];
    const testType = args[1] || 'unit';
    
    const tests = await this.getTestAgent().generateTests({
      sourceFile: filePath,
      testType: testType as any,
      coverage: 'comprehensive',
    });

    return {
      success: true,
      message: `Generated ${tests.tests.length} ${testType} tests`,
      data: tests,
    };
  }

  private async handleCodeCommand(args: string[], context: CommandContext): Promise<CommandResult> {
    if (args.length === 0) {
      return {
        success: false,
        message: 'Please specify a test file',
      };
    }

    const testFile = args[0];
    const code = await this.getCodeAgent().generateFromTests({
      testFile,
      targetFile: testFile.replace('.test.', '.').replace('.spec.', '.'),
      language: 'typescript',
    });

    return {
      success: true,
      message: 'Generated code from tests',
      data: code,
    };
  }

  private async handleVerifyCommand(args: string[], context: CommandContext): Promise<CommandResult> {
    const report = await this.getVerifyAgent().runFullVerification();
    
    return {
      success: report.overallStatus === 'passed',
      message: `Verification ${report.overallStatus}`,
      data: report,
    };
  }

  private async handleOperateCommand(args: string[], context: CommandContext): Promise<CommandResult> {
    if (args.length === 0) {
      return {
        success: false,
        message: 'Please specify an action (deploy, monitor, rollback)',
      };
    }

    const action = args[0];
    let result: any;

    switch (action) {
      case 'deploy':
        result = await this.getOperateAgent().deploy({
          environment: args[1] || 'production',
          strategy: 'blue-green',
        });
        break;
      case 'monitor':
        result = await this.getOperateAgent().getMetrics();
        break;
      case 'rollback':
        result = await this.getOperateAgent().rollback(args[1] || 'latest');
        break;
      default:
        return {
          success: false,
          message: `Unknown action: ${action}`,
        };
    }

    return {
      success: true,
      message: `Completed ${action}`,
      data: result,
    };
  }

  private async handleInitCommand(args: string[], context: CommandContext): Promise<CommandResult> {
    const projectName = args.join(' ') || 'New Project';
    
    const state = await context.phaseStateManager.initializeProject(projectName, true);
    
    return {
      success: true,
      message: `Initialized project: ${projectName}`,
      data: state,
      nextCommand: '/status',
    };
  }

  private async handleStatusCommand(args: string[], context: CommandContext): Promise<CommandResult> {
    const state = await context.phaseStateManager.getCurrentState();
    if (!state) {
      return {
        success: false,
        message: 'No project found. Use /init to create one.',
        nextCommand: '/init',
      };
    }

    const progress = await context.phaseStateManager.getProgressPercentage();
    const report = await context.phaseStateManager.generateStatusReport();

    return {
      success: true,
      message: report,
      data: {
        currentPhase: state.currentPhase,
        progress,
        state,
      },
    };
  }

  private async handleNextCommand(args: string[], context: CommandContext): Promise<CommandResult> {
    const canTransition = await context.phaseStateManager.canTransitionToNextPhase();
    
    if (!canTransition) {
      const state = await context.phaseStateManager.getCurrentState();
      const currentStatus = state?.phaseStatus[state.currentPhase];
      
      if (!currentStatus?.completed) {
        return {
          success: false,
          message: `Current phase ${state?.currentPhase} must be completed first`,
          nextCommand: `/complete`,
        };
      }
      
      if (state?.approvalsRequired && !currentStatus?.approved) {
        return {
          success: false,
          message: `Current phase ${state?.currentPhase} requires approval`,
          nextCommand: `/approve`,
        };
      }
    }

    const nextPhase = await context.phaseStateManager.transitionToNextPhase();
    
    if (!nextPhase) {
      return {
        success: true,
        message: 'All phases completed! Project is done.',
      };
    }

    return {
      success: true,
      message: `Transitioned to phase: ${nextPhase}`,
      data: { nextPhase },
      nextCommand: `/${nextPhase}`,
    };
  }

  private async handleApproveCommand(args: string[], context: CommandContext): Promise<CommandResult> {
    const state = await context.phaseStateManager.getCurrentState();
    if (!state) {
      return {
        success: false,
        message: 'No project found',
      };
    }

    const notes = args.join(' ');
    await context.approvalService.approve(
      state.currentPhase,
      'CLI User',
      notes || undefined
    );

    return {
      success: true,
      message: `Approved phase: ${state.currentPhase}`,
      nextCommand: '/next',
    };
  }

  private async handleCompleteCommand(args: string[], context: CommandContext): Promise<CommandResult> {
    const state = await context.phaseStateManager.getCurrentState();
    if (!state) {
      return {
        success: false,
        message: 'No project found',
      };
    }

    // Start phase if not started
    const phaseStatus = state.phaseStatus[state.currentPhase];
    if (!phaseStatus.startedAt) {
      await context.phaseStateManager.startPhase(state.currentPhase);
    }

    await context.phaseStateManager.completePhase(state.currentPhase, args);

    const message = state.approvalsRequired 
      ? `Completed phase: ${state.currentPhase}. Approval required.`
      : `Completed phase: ${state.currentPhase}`;

    return {
      success: true,
      message,
      nextCommand: state.approvalsRequired ? '/approve' : '/next',
    };
  }

  private async handleHelpCommand(args: string[], context: CommandContext): Promise<CommandResult> {
    if (args.length > 0) {
      // Show help for specific command
      const commandName = args[0];
      const resolvedName = this.aliases.get(commandName) || commandName;
      const command = this.commands.get(resolvedName);
      
      if (command) {
        let help = `Command: ${command.name}\n`;
        help += `Description: ${command.description}\n`;
        help += `Usage: ${command.usage}\n`;
        if (command.aliases) {
          help += `Aliases: ${command.aliases.join(', ')}\n`;
        }
        if (command.requiresPhase) {
          help += `Required Phase: ${command.requiresPhase}\n`;
        }
        
        return {
          success: true,
          message: help,
        };
      } else {
        return {
          success: false,
          message: `Unknown command: ${commandName}`,
        };
      }
    }

    // Show all commands grouped by category
    const categories = ['phase', 'workflow', 'info', 'utility'];
    let help = 'Available Commands:\n\n';

    for (const category of categories) {
      help += `${category.toUpperCase()} COMMANDS:\n`;
      
      for (const [name, command] of this.commands) {
        if (command.category === category) {
          help += `  ${name.padEnd(15)} - ${command.description}\n`;
        }
      }
      help += '\n';
    }

    help += 'Use /help <command> for detailed information about a specific command.';

    return {
      success: true,
      message: help,
    };
  }

  private async handleSteeringCommand(args: string[], context: CommandContext): Promise<CommandResult> {
    if (args.length === 0) {
      const docs = await context.steeringLoader.loadAllDocuments();
      const available = Object.keys(docs);
      
      return {
        success: true,
        message: `Available steering documents: ${available.join(', ')}`,
        data: docs,
      };
    }

    const action = args[0];
    const docName = args[1];

    switch (action) {
      case 'load':
        if (!docName) {
          return {
            success: false,
            message: 'Please specify document name',
          };
        }
        const content = await context.steeringLoader.loadDocument(docName);
        return {
          success: content !== null,
          message: content ? `Loaded ${docName}` : `Document ${docName} not found`,
          data: content,
        };
      
      case 'context':
        const steeringContext = await context.steeringLoader.getSteeringContext();
        return {
          success: true,
          message: 'Steering context loaded',
          data: steeringContext,
        };
      
      default:
        return {
          success: false,
          message: `Unknown action: ${action}. Use 'load' or 'context'`,
        };
    }
  }

  private async handleContextCommand(args: string[], context: CommandContext): Promise<CommandResult> {
    const state = await context.phaseStateManager.getCurrentState();
    const steeringContext = await context.steeringLoader.getSteeringContext();
    
    let message = 'Current Context:\n\n';
    
    if (state) {
      message += `Project: ${state.projectName || state.projectId}\n`;
      message += `Current Phase: ${state.currentPhase}\n`;
      message += `Progress: ${await context.phaseStateManager.getProgressPercentage()}%\n`;
    }
    
    message += `\nSteering Documents Available: ${steeringContext ? 'Yes' : 'No'}\n`;

    return {
      success: true,
      message,
      data: { state, steeringContext },
    };
  }

  private async handleTimelineCommand(args: string[], context: CommandContext): Promise<CommandResult> {
    const timeline = await context.phaseStateManager.getPhaseTimeline();
    
    let message = 'Phase Timeline:\n\n';
    
    for (const item of timeline) {
      const status = item.status === 'approved' ? '✅' :
                    item.status === 'completed' ? '✓' :
                    item.status === 'in-progress' ? '🚀' : '⏳';
      
      message += `${status} ${item.phase}: ${item.status}`;
      
      if (item.duration) {
        const minutes = Math.round(item.duration / 1000 / 60);
        message += ` (${minutes} min)`;
      }
      
      message += '\n';
    }

    return {
      success: true,
      message,
      data: timeline,
    };
  }

  private async handleRunCommand(args: string[], context: CommandContext): Promise<CommandResult> {
    if (args.length === 0) {
      return {
        success: false,
        message: 'Please specify a phase to run',
      };
    }

    const phase = args[0] as PhaseType;
    const validPhases = ['intent', 'formal', 'test', 'code', 'verify', 'operate'];
    
    if (!validPhases.includes(phase)) {
      return {
        success: false,
        message: `Invalid phase: ${phase}. Valid phases: ${validPhases.join(', ')}`,
      };
    }

    // Start the phase if not started
    const state = await context.phaseStateManager.getCurrentState();
    if (state && !state.phaseStatus[phase].startedAt) {
      await context.phaseStateManager.startPhase(phase);
    }

    return {
      success: true,
      message: `Running ${phase} phase workflow`,
      nextCommand: `/${phase}`,
    };
  }

  /**
   * Get list of available commands
   */
  getCommands(): SlashCommand[] {
    return Array.from(this.commands.values());
  }

  /**
   * Parse command from text (extract commands from natural text)
   */
  parseCommandFromText(text: string): string[] {
    const commands: string[] = [];
    /**
     * Regex pattern to extract slash commands from text.
     * 
     * Pattern explanation:
     *   /           - Match a literal slash
     *   \w+         - Match one or more word characters (the command name)
     *   (?:         - Start non-capturing group
     *     \s+       -   Match one or more whitespace characters
     *     [^/]*     -   Match zero or more characters that are not a slash (the arguments)
     *   )?          - End non-capturing group, make it optional (arguments are optional)
     *   g           - Global flag to match all occurrences
     * 
     * Examples of valid matches:
     *   "/run"                       => matches "/run"
     *   "/run intent"                => matches "/run intent"
     *   "/help"                      => matches "/help"
     *   "/set mode fast"             => matches "/set mode fast"
     *   "Please /run intent and /verify" => matches "/run intent", "/verify"
     * 
     * Examples of non-matches:
     *   "run intent"                 => no match (missing slash)
     *   "/ run"                      => no match (space after slash)
     */
    const pattern = /\/\w+(?:\s+[^/]*)?/g;
    const matches = text.match(pattern);
    
    if (matches) {
      commands.push(...matches.map(m => m.trim()));
    }
    
    return commands;
  }

  /**
   * Execute multiple commands in sequence
   */
  async executeSequence(commands: string[]): Promise<CommandResult[]> {
    const results: CommandResult[] = [];
    
    for (const command of commands) {
      const result = await this.execute(command);
      results.push(result);
      
      // Stop on failure unless the command is marked as non-critical
      if (!result.success) {
        const commandName = command.split(/\s+/)[0];
        const resolvedName = this.aliases.get(commandName) || commandName;
        const cmdObj = this.commands.get(resolvedName);
        const stopOnFailure = cmdObj?.stopOnFailure !== false;
        
        if (stopOnFailure) {
          break;
        }
      }
      
      // Execute next command if suggested
      if (result.nextCommand) {
        const nextResult = await this.execute(result.nextCommand);
        results.push(nextResult);
      }
    }
    
    return results;
  }
}