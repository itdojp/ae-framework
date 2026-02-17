/**
 * Domain Modeling Task Adapter type definitions
 * Extracted to keep implementation focused and reviewable.
 */

export interface DomainEntity {
  name: string;
  type: 'aggregate' | 'entity' | 'value_object' | 'service' | 'repository';
  description: string;
  attributes: EntityAttribute[];
  methods: EntityMethod[];
  relationships: EntityRelationship[];
  businessRules: string[];
  invariants: string[];
}

export interface EntityAttribute {
  name: string;
  type: string;
  required: boolean;
  description: string;
  constraints: string[];
}

export interface EntityMethod {
  name: string;
  parameters: Parameter[];
  returnType: string;
  description: string;
  businessRule?: string;
}

export interface Parameter {
  name: string;
  type: string;
  required: boolean;
}

export interface EntityRelationship {
  type: 'composition' | 'aggregation' | 'association' | 'inheritance' | 'dependency';
  target: string;
  cardinality: string;
  description: string;
}

export interface DomainModel {
  entities: DomainEntity[];
  boundedContexts: BoundedContext[];
  domainServices: DomainService[];
  aggregates: AggregateRoot[];
  ubiquitousLanguage: UbiquitousLanguageTerm[];
  businessRules: BusinessRule[];
}

export interface BoundedContext {
  name: string;
  description: string;
  entities: string[];
  services: string[];
  responsibilities: string[];
  interfaces: ContextInterface[];
}

export interface ContextInterface {
  name: string;
  type: 'command' | 'query' | 'event';
  description: string;
  contract: string;
}

export interface DomainService {
  name: string;
  description: string;
  operations: ServiceOperation[];
  dependencies: string[];
}

export interface ServiceOperation {
  name: string;
  description: string;
  inputs: Parameter[];
  outputs: Parameter[];
  businessRule: string;
}

export interface AggregateRoot {
  name: string;
  description: string;
  entities: string[];
  valueObjects: string[];
  businessRules: string[];
  invariants: string[];
}

export interface UbiquitousLanguageTerm {
  term: string;
  definition: string;
  context: string;
  synonyms: string[];
  relatedTerms: string[];
}

export interface BusinessRule {
  id: string;
  name: string;
  description: string;
  type: 'constraint' | 'derivation' | 'existence' | 'action_enabler';
  entities: string[];
  conditions: string[];
  actions: string[];
}

export interface DomainModelingInput {
  [key: string]: unknown;
}

export interface WarningLike {
  description: string;
}

export interface EntitySummary {
  name: string;
  type: string;
  description: string;
}

export interface BoundedContextSummary {
  name: string;
  description: string;
  entities: string[];
}

export interface NamedDescription {
  name: string;
  description: string;
}

export interface DomainComplexityAnalysis {
  high: string[];
  medium: string[];
  simple: string[];
}

export interface DomainAnalysisResult {
  entities: EntitySummary[];
  boundedContexts: BoundedContextSummary[];
  businessRules: NamedDescription[];
  domainServices: NamedDescription[];
  coreEntities: EntitySummary[];
  keyBusinessRules: NamedDescription[];
  complexityAnalysis: DomainComplexityAnalysis;
  complexityWarnings: WarningLike[];
  criticalGaps: string[];
}

export interface EntityRelationshipSummary {
  from: string;
  type: string;
  to: string;
  cardinality: string;
}

export interface EntityRuleCoverage {
  entity: string;
  rulesCount: number;
}

export interface EntityIdentificationResult {
  entities: EntitySummary[];
  aggregateRoots: string[];
  valueObjects: string[];
  domainServices: string[];
  relationships: EntityRelationshipSummary[];
  businessRuleCoverage: EntityRuleCoverage[];
  warnings: WarningLike[];
}

export interface AggregateSummary {
  name: string;
  description: string;
  entities: string[];
  valueObjects: string[];
  businessRules: string[];
  invariants: string[];
}

export interface AggregateBoundaryAnalysis {
  aggregate: string;
  boundaryStrength: string;
  cohesion: number;
}

export interface AggregateDependency {
  from: string;
  to: string;
  type: string;
  reason: string;
}

export interface AggregateModelingResult {
  aggregates: AggregateSummary[];
  boundaryAnalysis: AggregateBoundaryAnalysis[];
  dependencies: AggregateDependency[];
  boundaryWarnings: WarningLike[];
  criticalIssues: string[];
}

export interface ContextSummary {
  name: string;
  description: string;
  entities: string[];
  services: string[];
  responsibilities: string[];
}

export interface ContextRelationship {
  upstream: string;
  downstream: string;
  type: string;
}

export interface ContextIntegrationPattern {
  contexts: string[];
  pattern: string;
  description: string;
}

export interface BoundedContextDefinitionResult {
  contexts: ContextSummary[];
  relationships: ContextRelationship[];
  integrationPatterns: ContextIntegrationPattern[];
  integrationRisks: WarningLike[];
}

export interface RuleSummary {
  name: string;
  description: string;
  type: BusinessRule['type'];
  priority: 'high' | 'medium' | 'low';
}

export interface RuleComplexity {
  rule: string;
  complexity: string;
  dependencies: number;
}

export interface RuleEntityMapping {
  entity: string;
  rules: string[];
}

export interface BusinessRuleExtractionResult {
  rules: RuleSummary[];
  complexityAnalysis: RuleComplexity[];
  entityMapping: RuleEntityMapping[];
  conflictingRules: WarningLike[];
}

export interface LanguageTermSummary {
  term: string;
  definition: string;
  context: string;
}

export interface TermRelationshipSummary {
  term1: string;
  relationship: string;
  term2: string;
}

export interface UbiquitousLanguageResult {
  terms: LanguageTermSummary[];
  coreTerms: LanguageTermSummary[];
  supportingTerms: LanguageTermSummary[];
  termRelationships: TermRelationshipSummary[];
  ambiguousTerms: LanguageTermSummary[];
}

export interface DomainServiceSummary {
  name: string;
  description: string;
  operations: ServiceOperation[];
  dependencies: string[];
}

export interface ServiceDependencyAnalysis {
  service: string;
  dependencies: number;
  coupling: string;
}

export interface ServiceCohesionAnalysis {
  service: string;
  cohesion: number;
  responsibilities: number;
}

export interface DomainServiceDesignResult {
  services: DomainServiceSummary[];
  dependencyAnalysis: ServiceDependencyAnalysis[];
  cohesionAnalysis: ServiceCohesionAnalysis[];
  designIssues: WarningLike[];
}

export interface ValidationIssue {
  severity: string;
  description: string;
  category: string;
}

export interface ModelCompleteness {
  entities: number;
  relationships: number;
  businessRules: number;
  boundedContexts: number;
}

export interface ConsistencyCheckResult {
  category: string;
  status: string;
  issues: number;
}

export interface DomainModelValidationResult {
  score: number;
  entityValidation: number;
  relationshipValidation: number;
  businessRuleValidation: number;
  issues: ValidationIssue[];
  completeness: ModelCompleteness;
  consistencyChecks: ConsistencyCheckResult[];
  recommendations: string[];
  criticalIssues: WarningLike[];
}

export interface GenericDomainAnalysisResult {
  report: string;
  recommendations: string[];
  nextActions: string[];
  warnings: string[];
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

