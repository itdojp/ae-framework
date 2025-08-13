/**
 * Extended Commands for ae-framework
 * Unified architecture with consistent interfaces and shared functionality
 */

// Unified commands (new architecture)
export { UnifiedAnalyzeCommand } from './analyze-command-unified.js';
export { UnifiedDocumentCommand } from './document-command-unified.js';
export { UnifiedImproveCommand } from './improve-command-unified.js';
export { UnifiedTroubleshootCommand } from './troubleshoot-command-unified.js';

// Smart Persona System (Phase 2)
export { PersonaCommand } from './persona-command.js';

// Base classes and types
export { BaseExtendedCommand } from './base-command.js';
export type { ExtendedCommandResult, ExtendedCommandConfig, CommandMetrics } from './base-command.js';
export * from './types.js';