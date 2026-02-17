import type { Conflict, UserStory } from './interfaces/standard-interfaces.js';

export interface ValidationResult {
  isValid: boolean;
  score: number;
  issues: ValidationIssue[];
  recommendations: string[];
  coverageReport: CoverageReport;
}

export interface ValidationIssue {
  id: string;
  type: 'error' | 'warning' | 'info';
  severity: 'critical' | 'high' | 'medium' | 'low';
  category: string;
  description: string;
  location?: string;
  suggestion?: string;
}

export interface CoverageReport {
  functional: number;
  nonFunctional: number;
  business: number;
  technical: number;
  overall: number;
}

export type ValidationTaskType =
  | 'validate-requirements'
  | 'validate-user-stories'
  | 'validate-specifications'
  | 'validate-traceability'
  | 'validate-completeness'
  | 'validate-consistency'
  | 'validate-feasibility'
  | 'cross-validate';

export const VALIDATION_TASK_TYPES: ValidationTaskType[] = [
  'validate-requirements',
  'validate-user-stories',
  'validate-specifications',
  'validate-traceability',
  'validate-completeness',
  'validate-consistency',
  'validate-feasibility',
  'cross-validate',
];

export interface ValidationSourceItem {
  path: string;
  content: string;
}

export interface ValidationInput {
  requestedSources: string[];
  resolvedSources: ValidationSourceItem[];
  missingSources: string[];
  strict: boolean;
}

export interface ValidationIssueFrequency {
  description: string;
  frequency: number;
}

export interface ValidationStoryIssue {
  storyId: string;
  description: string;
}

export interface BlockingValidationIssue {
  description: string;
}

export interface UserStoriesQualityMetrics {
  formatCompliance: number;
  acceptanceCriteria: number;
  testability: number;
  independence: number;
  estimability: number;
}

export interface UserStoriesValidationResult {
  score: number;
  totalStories: number;
  validStories: number;
  qualityMetrics: UserStoriesQualityMetrics;
  commonIssues: ValidationIssueFrequency[];
  storyIssues: ValidationStoryIssue[];
  blockingIssues: BlockingValidationIssue[];
  validatedStories?: UserStory[];
  conflicts?: Conflict[];
  recommendations?: string[];
}

export interface SpecificationCompliance {
  formalNotation: number;
  completeness: number;
  consistency: number;
  clarity: number;
  testability: number;
}

export interface SpecificationGap {
  description: string;
  impact: string;
}

export interface SpecificationValidationResult {
  score: number;
  totalSpecs: number;
  compliance: SpecificationCompliance;
  issuesByCategory: Record<string, number>;
  criticalGaps: SpecificationGap[];
  recommendations: string[];
}

export interface TraceabilityMatrixEntry {
  source: string;
  targets: string[];
  coverage: number;
}

export interface TraceabilityLinkIssue {
  from: string;
  to: string;
  reason: string;
}

export interface BrokenTraceabilityLink {
  from: string;
  to: string;
}

export interface OrphanedTraceabilityArtifact {
  type: string;
  name: string;
}

export interface TraceabilityValidationResult {
  coveragePercentage: number;
  totalLinks: number;
  brokenLinks: BrokenTraceabilityLink[];
  matrix: TraceabilityMatrixEntry[];
  missingLinks: TraceabilityLinkIssue[];
  orphanedArtifacts: OrphanedTraceabilityArtifact[];
}

export interface CompletenessCategoryScore {
  name: string;
  score: number;
  missing: number;
}

export interface MissingComponent {
  category: string;
  description: string;
  priority: string;
}

export interface CompletenessTrend {
  improving: string[];
  declining: string[];
  stable: string[];
}

export interface CompletenessValidationResult {
  completenessScore: number;
  categoryScores: CompletenessCategoryScore[];
  missingComponents: MissingComponent[];
  trends: CompletenessTrend;
  recommendations: string[];
  criticalGaps: Array<{ description: string }>;
}

export interface MajorInconsistency {
  type: string;
  description: string;
  location: string;
}

export interface TerminologyConflict {
  term: string;
  definitions: string[];
}

export interface ConsistencyValidationResult {
  consistencyScore: number;
  inconsistencies: MajorInconsistency[];
  terminologyConsistency: number;
  formatConsistency: number;
  businessRuleConsistency: number;
  technicalConsistency: number;
  majorInconsistencies: MajorInconsistency[];
  terminologyConflicts: TerminologyConflict[];
  recommendations: string[];
}

export interface FeasibilityRiskFactor {
  category: string;
  description: string;
  impact: string;
  probability: string;
}

export interface InfeasibleRequirement {
  id: string;
  reason: string;
  alternative: string;
}

export interface FeasibilityValidationResult {
  feasibilityScore: number;
  technical: number;
  economic: number;
  operational: number;
  schedule: number;
  riskFactors: FeasibilityRiskFactor[];
  infeasibleRequirements: InfeasibleRequirement[];
  highRiskFactors: FeasibilityRiskFactor[];
  recommendations: string[];
}

export interface PhaseAlignmentScore {
  name: string;
  score: number;
}

export interface CrossPhaseIssue {
  phases: string[];
  description: string;
  severity: string;
}

export interface AlignmentGap {
  description: string;
  phases: string[];
}

export interface CrossValidationResult {
  overallScore: number;
  phaseAlignment: PhaseAlignmentScore[];
  crossPhaseIssues: CrossPhaseIssue[];
  alignmentGaps: AlignmentGap[];
  criticalIssues: Array<{ description: string }>;
  recommendations: string[];
}

export interface GenericValidationResult {
  report: string;
  recommendations: string[];
  nextActions: string[];
  warnings: string[];
  hasBlockingIssues: boolean;
}

export interface ProactiveGuidanceContext {
  recentFiles: string[];
  recentActions: string[];
  userIntent: string;
}

export interface ProactiveGuidanceResult {
  shouldIntervene: boolean;
  intervention: {
    type: 'warning' | 'suggestion' | 'block';
    message: string;
    recommendedActions: string[];
  };
}
