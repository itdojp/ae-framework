/**
 * CEGIS Module Exports
 * Phase 2.1: Main exports for Counter-Example Guided Inductive Synthesis
 */
export * from './types.js';
export { FailureArtifactFactory } from './failure-artifact-factory.js';
export { AutoFixEngine } from './auto-fix-engine.js';
export { RiskAssessmentService } from './risk-assessment-service.js';
export { BaseFixStrategy } from './strategies/base-strategy.js';
export { TypeErrorFixStrategy } from './strategies/type-error-strategy.js';
export { TestFailureFixStrategy } from './strategies/test-failure-strategy.js';
export { ContractViolationFixStrategy } from './strategies/contract-violation-strategy.js';
export { CEGISCli, executeCEGISCli } from '../cli/cegis-cli.js';
