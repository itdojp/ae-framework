import { readFileSync } from 'fs';
import { join } from 'path';

/**
 * Supported AE-Framework phases
 */
const PHASES = ['phase-1', 'phase-2', 'phase-3', 'phase-4', 'phase-5', 'phase-6'] as const;

/**
 * Quality Policy Configuration Types
 */
export interface QualityThresholds {
  lines?: number;
  functions?: number;
  branches?: number;
  statements?: number;
  critical?: number;
  serious?: number;
  moderate?: number;
  minor?: number;
  total_warnings?: number;
  errors?: number;
  warnings?: number;
  performance?: number;
  accessibility?: number;
  bestPractices?: number;
  seo?: number;
  pwa?: string;
  pixelDifference?: number;
  failureThreshold?: number;
  uiViolations?: number;
  designSystemViolations?: number;
  accessibilityViolations?: number;
  mutationScore?: number;
  survived?: number;
  testToCodeRatio?: number;
  redGreenCycleCompliance?: number;
  high?: number;
  low?: number;
}

export interface QualityGate {
  description: string;
  enforcement: 'strict' | 'warn' | 'off';
  thresholds: QualityThresholds;
  tools: string[];
  phases: string[];
  enabledFromPhase?: string;
  excludePatterns?: string[];
  config?: Record<string, any>;
  targetPaths?: string[];
}

export interface QualityPolicy {
  $schema?: string;
  $id?: string;
  title: string;
  description: string;
  version: string;
  lastUpdated: string;
  quality: Record<string, QualityGate>;
  environments: Record<string, {
    description: string;
    overrides: Record<string, any>;
  }>;
  reporting: {
    outputDirectory: string;
    formats: string[];
    retention: {
      days: number;
      artifacts: string[];
    };
  };
  notifications: {
    onFailure: Record<string, any>;
    onThresholdChange: {
      requireApproval: boolean;
      reviewers: string[];
    };
  };
}

/**
 * Get the current quality profile from environment variable or parameter
 * @param environment - Optional environment override
 * @returns Profile name ('development', 'ci', 'production')
 */
export const getQualityProfile = (environment?: string): string => {
  return environment || process.env.AE_QUALITY_PROFILE || 'ci';
};

/**
 * Loads the centralized quality policy configuration
 * @param environment - Optional environment to apply overrides ('development', 'ci', 'production')
 * @returns Parsed quality policy with environment overrides applied
 */
export const loadQualityPolicy = (environment?: string): QualityPolicy => {
  try {
    const policyPath = join(process.cwd(), 'policy', 'quality.json');
    const policyContent = readFileSync(policyPath, 'utf-8');
    const policy: QualityPolicy = JSON.parse(policyContent);
    
    // Apply environment-specific overrides based on profile
    const activeProfile = getQualityProfile(environment);
    if (activeProfile && policy.environments[activeProfile]) {
      const overrides = policy.environments[activeProfile].overrides;
      policy.quality = applyOverrides(policy.quality, overrides);
    }
    
    return policy;
  } catch (error) {
    throw new Error(`Failed to load quality policy: ${error instanceof Error ? error.message : String(error)}`);
  }
};

/**
 * Get quality gate configuration for a specific gate type
 * @param gateType - The type of quality gate (e.g., 'accessibility', 'coverage', 'lighthouse')
 * @param environment - Optional environment for overrides
 * @returns Quality gate configuration
 */
export const getQualityGate = (gateType: string, environment?: string): QualityGate => {
  const policy = loadQualityPolicy(environment);
  const gate = policy.quality[gateType];
  
  if (!gate) {
    throw new Error(`Quality gate '${gateType}' not found in policy configuration`);
  }
  
  return gate;
};

/**
 * Check if a quality gate should be enforced for the current phase
 * @param gateType - The type of quality gate
 * @param currentPhase - Current development phase
 * @param environment - Optional environment for overrides
 * @returns True if the gate should be enforced
 */
export const shouldEnforceGate = (gateType: string, currentPhase: string, environment?: string): boolean => {
  const gate = getQualityGate(gateType, environment);
  
  // Check if enforcement is disabled
  if (gate.enforcement === 'off') {
    return false;
  }
  
  // Check if the gate applies to the current phase
  if (gate.phases && gate.phases.length > 0) {
    return gate.phases.includes(currentPhase);
  }
  
  // Check if there's an enabled from phase requirement
  if (gate.enabledFromPhase) {
    const enabledPhaseIndex = PHASES.indexOf(gate.enabledFromPhase);
    const currentPhaseIndex = PHASES.indexOf(currentPhase);
    
    return currentPhaseIndex >= enabledPhaseIndex;
  }
  
  return true;
};

/**
 * Get threshold value for a specific quality gate and metric
 * @param gateType - The type of quality gate
 * @param metric - The specific metric name
 * @param environment - Optional environment for overrides
 * @returns The threshold value
 */
export const getThreshold = (gateType: string, metric: string, environment?: string): number | string | undefined => {
  const gate = getQualityGate(gateType, environment);
  return gate.thresholds[metric as keyof QualityThresholds];
};

/**
 * Generate command line arguments for threshold-based tools
 * @param gateType - The type of quality gate
 * @param environment - Optional environment for overrides
 * @returns Array of command line arguments
 */
export const getThresholdArgs = (gateType: string, environment?: string): string[] => {
  const gate = getQualityGate(gateType, environment);
  const args: string[] = [];
  
  Object.entries(gate.thresholds).forEach(([key, value]) => {
    if (typeof value === 'number' || typeof value === 'string') {
      // Convert camelCase to kebab-case for CLI args
      const argName = key.replace(/([A-Z])/g, '-$1').toLowerCase();
      args.push(`--${argName}=${value}`);
    }
  });
  
  return args;
};

/**
 * Validate quality gate results against policy thresholds
 * @param gateType - The type of quality gate
 * @param results - The results to validate
 * @param environment - Optional environment for overrides
 * @returns Validation result with pass/fail status and messages
 */
export const validateQualityResults = (
  gateType: string, 
  results: Record<string, number>, 
  environment?: string
): { passed: boolean; failures: string[]; warnings: string[] } => {
  const gate = getQualityGate(gateType, environment);
  const failures: string[] = [];
  const warnings: string[] = [];
  
  Object.entries(gate.thresholds).forEach(([metric, threshold]) => {
    const actualValue = results[metric];
    
    if (actualValue !== undefined && typeof threshold === 'number') {
      const passed = isThresholdMet(metric, actualValue, threshold);
      
      if (!passed) {
        const message = `${metric}: ${actualValue} (threshold: ${getThresholdComparison(metric)}${threshold})`;
        
        if (gate.enforcement === 'strict') {
          failures.push(message);
        } else if (gate.enforcement === 'warn') {
          warnings.push(message);
        }
      }
    }
  });
  
  return {
    passed: failures.length === 0,
    failures,
    warnings
  };
};

/**
 * Apply environment overrides to quality configuration
 * @param quality - Original quality configuration
 * @param overrides - Environment-specific overrides
 * @returns Updated quality configuration
 */
function applyOverrides(quality: Record<string, QualityGate>, overrides: Record<string, any>): Record<string, QualityGate> {
  const updatedQuality = JSON.parse(JSON.stringify(quality)); // Deep clone
  
  Object.entries(overrides).forEach(([path, value]) => {
    const pathParts = path.split('.');
    let current = updatedQuality;
    
    // Navigate to the parent object
    for (let i = 0; i < pathParts.length - 1; i++) {
      const part = pathParts[i];
      if (current[part] === undefined) {
        current[part] = {};
      }
      current = current[part];
    }
    
    // Set the final value
    const finalKey = pathParts[pathParts.length - 1];
    current[finalKey] = value;
  });
  
  return updatedQuality;
}

/**
 * Check if a threshold is met based on the metric type
 * @param metric - The metric name
 * @param actual - The actual value
 * @param threshold - The threshold value
 * @returns True if threshold is met
 */
function isThresholdMet(metric: string, actual: number, threshold: number): boolean {
  // For most metrics, higher is better (coverage, performance scores)
  // For violations/errors, lower is better
  const lowerIsBetterMetrics = [
    'critical', 'serious', 'moderate', 'minor', 'total_warnings', 
    'errors', 'warnings', 'pixelDifference', 'failureThreshold',
    'uiViolations', 'designSystemViolations', 'accessibilityViolations',
    'survived', 'high', 'low'
  ];
  
  return lowerIsBetterMetrics.includes(metric) 
    ? actual <= threshold 
    : actual >= threshold;
}

/**
 * Get comparison operator for displaying threshold comparisons
 * @param metric - The metric name
 * @returns Comparison operator string
 */
function getThresholdComparison(metric: string): string {
  const lowerIsBetterMetrics = [
    'critical', 'serious', 'moderate', 'minor', 'total_warnings', 
    'errors', 'warnings', 'pixelDifference', 'failureThreshold',
    'uiViolations', 'designSystemViolations', 'accessibilityViolations',
    'survived', 'high', 'low'
  ];
  
  return lowerIsBetterMetrics.includes(metric) ? '≤' : '≥';
}

/**
 * Get current development phase from project state
 * @returns Current phase identifier
 */
export const getCurrentPhase = (): string => {
  try {
    const phaseStatePath = join(process.cwd(), '.ae', 'phase-state.json');
    const phaseState = JSON.parse(readFileSync(phaseStatePath, 'utf-8'));
    return phaseState.currentPhase || 'phase-1';
  } catch {
    return 'phase-1'; // Default to phase-1 if no state file
  }
};

/**
 * Export main function for backward compatibility and CLI usage
 */
export default loadQualityPolicy;