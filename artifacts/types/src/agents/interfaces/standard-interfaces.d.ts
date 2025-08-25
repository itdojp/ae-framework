/**
 * Standard AE Framework Agent Interfaces
 * Provides consistent input/output patterns for agent pipeline integration
 */
/**
 * Standard processing context shared across all agents
 */
export interface ProcessingContext {
    projectId?: string;
    domain?: string;
    previousPhaseResults?: PhaseResult[];
    metadata?: Record<string, any>;
    requestId?: string;
    timestamp?: string;
}
/**
 * Standardized phase result wrapper
 */
export interface PhaseResult<T = any> {
    success: boolean;
    data: T;
    metadata: PhaseMetadata;
    errors?: AgentError[];
    warnings?: string[];
    phase: PhaseType;
}
/**
 * Phase execution metadata
 */
export interface PhaseMetadata {
    phase: PhaseType;
    agentName: string;
    startTime: Date;
    endTime: Date;
    duration: number;
    version: string;
    inputHash?: string;
    confidence?: number;
}
/**
 * Standardized error format
 */
export interface AgentError {
    code: string;
    message: string;
    phase: PhaseType;
    severity: 'error' | 'warning' | 'info';
    context?: Record<string, any>;
    stack?: string;
}
/**
 * Phase types supported by the AE Framework pipeline
 */
export type PhaseType = 'intent' | 'requirements' | 'user-stories' | 'validation' | 'domain-modeling' | 'ui-ux-generation';
/**
 * Standard agent interface - all AE Framework agents should implement this
 */
export interface StandardAEAgent<TInput = any, TOutput = any> {
    readonly agentName: string;
    readonly version: string;
    readonly supportedPhase: PhaseType;
    /**
     * Main processing method - standardized across all agents
     */
    process(input: TInput, context?: ProcessingContext): Promise<PhaseResult<TOutput>>;
    /**
     * Validate input before processing
     */
    validateInput(input: TInput): ValidationResult;
    /**
     * Get agent metadata and capabilities
     */
    getCapabilities(): AgentCapabilities;
}
/**
 * Input validation result
 */
export interface ValidationResult {
    valid: boolean;
    errors: string[];
    warnings: string[];
}
/**
 * Agent capabilities description
 */
export interface AgentCapabilities {
    supportedInputTypes: string[];
    outputSchema: string;
    requiredContext: string[];
    optionalContext: string[];
    maxInputSize?: number;
    estimatedProcessingTime?: number;
}
/**
 * Pipeline data flow interfaces
 */
export interface IntentInput {
    sources: RequirementSource[];
    context?: ProjectContext;
}
export interface IntentOutput {
    primaryIntent: string;
    requirements: Requirement[];
    stakeholders: Stakeholder[];
    constraints: Constraint[];
    businessContext: BusinessContext;
    confidenceScore: number;
}
export interface RequirementsInput {
    intentAnalysis: IntentOutput;
    additionalRequirements?: string;
}
export interface RequirementsOutput {
    structured: StructuredRequirement[];
    summary: string;
    gaps: string[];
    processedRequirements: string;
    naturalLanguageRequirements: string;
}
export interface UserStoriesInput {
    requirements: RequirementsOutput;
    stakeholders: Stakeholder[];
}
export interface UserStoriesOutput {
    stories: UserStory[];
    acceptanceCriteria: AcceptanceCriteria[];
    traceabilityMatrix: TraceabilityMatrix;
    success: boolean;
}
export interface ValidationInput {
    userStories: UserStoriesOutput;
    requirements: RequirementsOutput;
    constraints: Constraint[];
}
export interface ValidationOutput {
    validatedStories: UserStory[];
    validationReport: ValidationReport;
    conflicts: Conflict[];
    recommendations: string[];
}
export interface DomainModelingInput {
    validatedUserStories: ValidationOutput;
    requirements: RequirementsOutput;
    businessContext: BusinessContext;
}
export interface DomainModelingOutput {
    entities: DomainEntity[];
    relationships: EntityRelationship[];
    valueObjects: ValueObject[];
    aggregates: Aggregate[];
    services: DomainService[];
    boundedContexts: BoundedContext[];
}
export interface UIUXInput {
    domainModel: DomainModelingOutput;
    userStories: UserStoriesOutput;
    stakeholders: Stakeholder[];
}
export interface UIUXOutput {
    wireframes: Wireframe[];
    userFlows: UserFlow[];
    components: UIComponent[];
    designSystem: DesignSystem;
    prototypes: Prototype[];
}
/**
 * Supporting type definitions
 */
export interface RequirementSource {
    type: 'text' | 'document' | 'specification' | 'conversation';
    content: string;
    metadata?: Record<string, any>;
}
export interface ProjectContext {
    domain: string;
    organization?: string;
    existingSystem?: boolean;
    constraints?: Constraint[];
    stakeholders?: Stakeholder[];
    glossary?: GlossaryTerm[];
}
export interface Requirement {
    id: string;
    description: string;
    type: 'functional' | 'non-functional' | 'constraint';
    priority: 'must' | 'should' | 'could' | 'won\'t';
    source: string;
    acceptance_criteria: string[];
}
export interface Stakeholder {
    name: string;
    role: string;
    concerns: string[];
    influenceLevel: 'high' | 'medium' | 'low';
}
export interface Constraint {
    type: 'technical' | 'business' | 'regulatory' | 'resource';
    description: string;
    impact: 'high' | 'medium' | 'low';
    source?: string;
}
export interface BusinessContext {
    domain: string;
    businessModel: string;
    keyProcesses: string[];
    success_metrics: string[];
    assumptions: string[];
}
export interface GlossaryTerm {
    term: string;
    definition: string;
    context?: string;
}
export interface StructuredRequirement extends Requirement {
    category: string;
    dependencies: string[];
    risks: string[];
}
export interface UserStory {
    id: string;
    title: string;
    description: string;
    asA: string;
    iWant: string;
    soThat: string;
    acceptanceCriteria: string[];
    priority: 'high' | 'medium' | 'low';
    storyPoints?: number;
    tags?: string[];
}
export interface AcceptanceCriteria {
    storyId: string;
    criteria: string[];
    testScenarios: TestScenario[];
}
export interface TestScenario {
    given: string;
    when: string;
    then: string;
}
export interface TraceabilityMatrix {
    requirements: Record<string, string[]>;
    coverage: number;
    gaps: string[];
}
export interface ValidationReport {
    totalStories: number;
    validatedStories: number;
    conflicts: number;
    coverage: number;
    quality_score: number;
}
export interface Conflict {
    type: 'requirement' | 'story' | 'constraint';
    description: string;
    affected: string[];
    severity: 'high' | 'medium' | 'low';
    recommendation: string;
}
export interface DomainEntity {
    name: string;
    attributes: EntityAttribute[];
    methods: EntityMethod[];
    invariants: string[];
    isAggregateRoot: boolean;
}
export interface EntityAttribute {
    name: string;
    type: string;
    required: boolean;
    description?: string;
}
export interface EntityMethod {
    name: string;
    parameters: MethodParameter[];
    returnType: string;
    description: string;
}
export interface MethodParameter {
    name: string;
    type: string;
    required: boolean;
}
export interface EntityRelationship {
    from: string;
    to: string;
    type: 'one-to-one' | 'one-to-many' | 'many-to-many';
    description: string;
}
export interface ValueObject {
    name: string;
    attributes: EntityAttribute[];
    invariants: string[];
}
export interface Aggregate {
    name: string;
    root: string;
    entities: string[];
    valueObjects: string[];
    invariants: string[];
}
export interface DomainService {
    name: string;
    methods: EntityMethod[];
    dependencies: string[];
}
export interface BoundedContext {
    name: string;
    description: string;
    entities: string[];
    services: string[];
    aggregates: string[];
}
export interface Wireframe {
    name: string;
    type: 'low-fidelity' | 'high-fidelity';
    components: WireframeComponent[];
    userFlow: string;
}
export interface WireframeComponent {
    type: string;
    properties: Record<string, any>;
    children?: WireframeComponent[];
}
export interface UserFlow {
    name: string;
    steps: UserFlowStep[];
    triggers: string[];
    outcomes: string[];
}
export interface UserFlowStep {
    action: string;
    screen: string;
    nextStep?: string;
    conditions?: string[];
}
export interface UIComponent {
    name: string;
    type: string;
    props: ComponentProp[];
    states: ComponentState[];
    interactions: ComponentInteraction[];
}
export interface ComponentProp {
    name: string;
    type: string;
    required: boolean;
    description?: string;
}
export interface ComponentState {
    name: string;
    description: string;
    triggers: string[];
}
export interface ComponentInteraction {
    event: string;
    action: string;
    feedback: string;
}
export interface DesignSystem {
    colors: Record<string, string>;
    typography: TypographyScale;
    spacing: SpacingScale;
    components: ComponentLibrary;
}
export interface TypographyScale {
    fonts: Record<string, string>;
    sizes: Record<string, string>;
    weights: Record<string, number>;
}
export interface SpacingScale {
    base: number;
    scale: Record<string, number>;
}
export interface ComponentLibrary {
    [componentName: string]: UIComponent;
}
export interface Prototype {
    name: string;
    type: 'static' | 'interactive';
    screens: Screen[];
    interactions: PrototypeInteraction[];
}
export interface Screen {
    name: string;
    wireframe: string;
    components: UIComponent[];
}
export interface PrototypeInteraction {
    from: string;
    to: string;
    trigger: string;
    transition: string;
}
