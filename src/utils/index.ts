/**
 * Utility modules for ae-framework
 */

export { PhaseStateManager } from './phase-state-manager.js';
export { SteeringLoader } from './steering-loader.js';
export { EvidenceValidator } from './evidence-validator.js';
export { TokenOptimizer } from './token-optimizer.js';
export { ContextManager } from './context-manager.js';
export { parseComparator, compare, strictest } from './comparator.js';

// Smart Persona System (Phase 2)
export { PersonaManager } from './persona-manager.js';
export type { 
  UserPreferences,
  WorkingContext,
  PersonaProfile,
  AdaptationRule,
  LearningData 
} from './persona-manager.js';
