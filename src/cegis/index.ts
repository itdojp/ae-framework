/**
 * CEGIS Module Exports
 * Phase 2.1: Main exports for Counter-Example Guided Inductive Synthesis
 */

// Core types
export * from './types.js';

// Failure artifact management
export { FailureArtifactFactory } from './failure-artifact-factory.js';

// Auto-fix engine
export { AutoFixEngine } from './auto-fix-engine.js';

// Risk assessment
export { RiskAssessmentService } from './risk-assessment-service.js';

// Fix strategies
export { BaseFixStrategy } from './strategies/base-strategy.js';
export { TypeErrorFixStrategy } from './strategies/type-error-strategy.js';
export { TestFailureFixStrategy } from './strategies/test-failure-strategy.js';
export { ContractViolationFixStrategy } from './strategies/contract-violation-strategy.js';

// CLI
export { CEGISCli, executeCEGISCli } from '../cli/cegis-cli.js';