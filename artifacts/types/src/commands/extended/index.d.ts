/**
 * Extended Commands for ae-framework
 * Unified architecture with consistent interfaces and shared functionality
 */
export { UnifiedAnalyzeCommand } from './analyze-command-unified.js';
export { UnifiedDocumentCommand } from './document-command-unified.js';
export { UnifiedImproveCommand } from './improve-command-unified.js';
export { UnifiedTroubleshootCommand } from './troubleshoot-command-unified.js';
export { PersonaCommand } from './persona-command.js';
export { InstallerCommand } from './installer-command.js';
export { MCPCommand } from './mcp-command.js';
export { BaseExtendedCommand } from './base-command.js';
export type { ExtendedCommandResult, ExtendedCommandConfig, CommandMetrics } from './base-command.js';
export * from './types.js';
