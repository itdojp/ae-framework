/**
 * Persona Command for ae-framework
 * Manages Smart Persona System for adaptive AI behavior
 */
import { BaseExtendedCommand, ExtendedCommandResult } from './base-command.js';
import type { CommandContext } from '../slash-command-manager.js';
import { UserPreferences, PersonaProfile } from '../../utils/persona-manager.js';
interface PersonaCommandResult {
    action: 'view' | 'update' | 'export' | 'import' | 'reset';
    profile?: PersonaProfile;
    preferences?: UserPreferences;
    message: string;
    data?: any;
}
export declare class PersonaCommand extends BaseExtendedCommand {
    private personaManager;
    constructor();
    protected validateArgs(args: string[]): {
        isValid: boolean;
        message?: string;
    };
    protected parseOptions(args: string[]): Record<string, any>;
    protected execute(args: string[], options: any, context: CommandContext): Promise<ExtendedCommandResult<PersonaCommandResult>>;
    private handleView;
    private handleUpdate;
    private handleExport;
    private handleImport;
    private handleReset;
    private parseUpdateOptions;
    private convertUpdateTypes;
    private getAvailablePreferenceKeys;
    protected generateValidationClaim(data: PersonaCommandResult): string;
    protected generateSummary(data: PersonaCommandResult): string;
}
export {};
