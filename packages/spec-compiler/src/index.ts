/**
 * @ae-framework/spec-compiler
 * 
 * AE-Spec to AE-IR compiler for single source of truth (SSOT)
 * Transforms natural language specifications into structured intermediate representation
 */

export { AESpecCompiler } from './compiler.js';
export type {
  AEIR,
  SpecLintReport,
  SpecLintIssue,
  CompileOptions,
  LintOptions,
} from './types.js';

// Re-export for convenience
export interface AESpecCompilerInterface {
  compile(options: import('./types.js').CompileOptions): Promise<import('./types.js').AEIR>;
  lint(ir: import('./types.js').AEIR): Promise<import('./types.js').SpecLintReport>;
}

// Default export for easy importing
import { AESpecCompiler } from './compiler.js';
export default AESpecCompiler;