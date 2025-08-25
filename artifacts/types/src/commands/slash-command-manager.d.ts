/**
 * Slash Command Manager for ae-framework
 * Provides a unified interface for executing commands across all agents
 */
import { PhaseStateManager, PhaseType } from '../utils/phase-state-manager.js';
import { SteeringLoader } from '../utils/steering-loader.js';
import { ApprovalService } from '../services/approval-service.js';
export interface SlashCommand {
    name: string;
    description: string;
    category: 'phase' | 'utility' | 'info' | 'workflow';
    usage: string;
    aliases?: string[];
    handler: CommandHandler;
    requiresPhase?: PhaseType;
    stopOnFailure?: boolean;
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
export declare class SlashCommandManager {
    private commands;
    private aliases;
    private context;
    private intentAgent?;
    private formalAgent?;
    private testAgent?;
    private codeAgent?;
    private verifyAgent?;
    private operateAgent?;
    constructor(projectRoot?: string);
    /**
     * Get or create intent agent
     */
    private getIntentAgent;
    /**
     * Get or create formal agent
     */
    private getFormalAgent;
    /**
     * Get or create test agent
     */
    private getTestAgent;
    /**
     * Get or create code agent
     */
    private getCodeAgent;
    /**
     * Get or create verify agent
     */
    private getVerifyAgent;
    /**
     * Get or create operate agent
     */
    private getOperateAgent;
    /**
     * Register extended commands from Issue #17 (Unified Architecture)
     */
    private registerExtendedCommands;
    /**
     * Register all available commands
     */
    private registerCommands;
    /**
     * Register a command
     */
    private registerCommand;
    /**
     * Execute a command
     */
    execute(input: string): Promise<CommandResult>;
    private handleIntentCommand;
    private handleFormalCommand;
    private handleTestCommand;
    private handleCodeCommand;
    private handleVerifyCommand;
    private handleOperateCommand;
    private handleInitCommand;
    private handleStatusCommand;
    private handleNextCommand;
    private handleApproveCommand;
    private handleCompleteCommand;
    private handleHelpCommand;
    private handleSteeringCommand;
    private handleContextCommand;
    private handleTimelineCommand;
    private handleRunCommand;
    /**
     * Get list of available commands
     */
    getCommands(): SlashCommand[];
    /**
     * Parse command from text (extract commands from natural text)
     */
    parseCommandFromText(text: string): string[];
    /**
     * Execute multiple commands in sequence
     */
    executeSequence(commands: string[]): Promise<CommandResult[]>;
}
