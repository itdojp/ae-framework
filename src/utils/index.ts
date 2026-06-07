/**
 * Utility modules for ae-framework
 */

export { PhaseStateManager } from './phase-state-manager.js';
export { SteeringLoader } from './steering-loader.js';
export { EvidenceValidator } from './evidence-validator.js';
export { TokenOptimizer } from './token-optimizer.js';
export { ContextManager } from './context-manager.js';
export { compare, parseComparator, strictest } from './comparator.js';
export type { ComparatorBaseUnit, ComparatorOperator, ParsedComparator } from './comparator.js';
export {
  DEFAULT_HIGH_IMPACT_APPROVAL_SCOPES,
  createHighImpactChildEnv,
  evaluateHighImpactActionPolicy,
  findAmbientSecretNames,
  formatHighImpactDecisionMessage,
  isHighImpactAgentContext,
  isHighImpactCiContext,
  isHighImpactUntrustedCheckout,
} from './high-impact-action-policy.js';
export type {
  HighImpactActionApproval,
  HighImpactActionKind,
  HighImpactActionPolicyDecision,
  HighImpactActionPolicyInput,
} from './high-impact-action-policy.js';

// Smart Persona System (Phase 2)
export { PersonaManager } from './persona-manager.js';
export type { 
  UserPreferences,
  WorkingContext,
  PersonaProfile,
  AdaptationRule,
  LearningData 
} from './persona-manager.js';
