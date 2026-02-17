export interface IntentAnalysisRequest {
  sources: RequirementSource[];
  context?: ProjectContext;
  analysisDepth?: 'basic' | 'detailed' | 'comprehensive';
  outputFormat?: 'structured' | 'narrative' | 'both';
}

export interface RequirementSource {
  type: 'text' | 'document' | 'conversation' | 'issue' | 'email' | 'diagram';
  content: string;
  metadata?: SourceMetadata;
}

export interface SourceMetadata {
  author?: string;
  date?: Date;
  priority?: 'critical' | 'high' | 'medium' | 'low';
  tags?: string[];
  references?: string[];
}

export interface ProjectContext {
  domain: string;
  existingSystem?: boolean;
  constraints?: Constraint[];
  stakeholders?: Stakeholder[];
  glossary?: GlossaryTerm[];
}

export interface Constraint {
  type: 'technical' | 'business' | 'regulatory' | 'resource';
  description: string;
  impact: 'high' | 'medium' | 'low';
  source?: string;
}

export interface Stakeholder {
  name: string;
  role: string;
  concerns: string[];
  influenceLevel: 'high' | 'medium' | 'low';
}

export interface GlossaryTerm {
  term: string;
  definition: string;
  context?: string;
}

export interface IntentAnalysisResult {
  requirements: Requirement[];
  userStories: UserStory[];
  useCases: UseCase[];
  constraints: Constraint[];
  assumptions: Assumption[];
  risks: Risk[];
  domainModel: DomainModel;
  ambiguities: Ambiguity[];
  suggestions: string[];
  traceability: RequirementTrace[];
  primaryIntent: string;
}

export interface Requirement {
  id: string;
  type: 'functional' | 'non-functional' | 'business' | 'technical';
  category: string;
  description: string;
  rationale?: string;
  priority: 'must' | 'should' | 'could' | 'wont';
  acceptance: AcceptanceCriteria[];
  source: string;
  status: 'draft' | 'reviewed' | 'approved' | 'implemented';
  dependencies?: string[];
}

export interface AcceptanceCriteria {
  given: string;
  when: string;
  then: string;
}

export interface UserStory {
  id: string;
  title: string;
  narrative: {
    asA: string;
    iWant: string;
    soThat: string;
  };
  acceptance: AcceptanceCriteria[];
  points?: number;
  priority: 'high' | 'medium' | 'low';
  requirements: string[];
}

export interface UseCase {
  id: string;
  name: string;
  actors: string[];
  preconditions: string[];
  mainFlow: Step[];
  alternativeFlows: Flow[];
  postconditions: string[];
  exceptions: Exception[];
}

export interface Step {
  number: number;
  actor: string;
  action: string;
  system: string;
}

export interface Flow {
  name: string;
  trigger: string;
  steps: Step[];
}

export interface Exception {
  condition: string;
  handling: string;
}

export interface Assumption {
  id: string;
  description: string;
  impact: 'high' | 'medium' | 'low';
  validation: string;
}

export interface Risk {
  id: string;
  description: string;
  probability: 'high' | 'medium' | 'low';
  impact: 'high' | 'medium' | 'low';
  mitigation: string;
}

export interface DomainModel {
  entities: Entity[];
  relationships: Relationship[];
  boundedContexts: BoundedContext[];
  aggregates: Aggregate[];
}

export interface Entity {
  name: string;
  attributes: Attribute[];
  behaviors: string[];
  invariants: string[];
}

export interface Attribute {
  name: string;
  type: string;
  required: boolean;
  constraints?: string[];
}

export interface Relationship {
  from: string;
  to: string;
  type: 'has' | 'uses' | 'contains' | 'references';
  cardinality: '1-1' | '1-n' | 'n-1' | 'n-n';
}

export interface BoundedContext {
  name: string;
  entities: string[];
  ubiquitousLanguage: GlossaryTerm[];
}

export interface Aggregate {
  root: string;
  entities: string[];
  invariants: string[];
}

export interface Ambiguity {
  text: string;
  type: 'vague' | 'conflicting' | 'incomplete' | 'undefined';
  location: string;
  suggestion: string;
  severity: 'high' | 'medium' | 'low';
}

export interface RequirementTrace {
  requirementId: string;
  linkedTo: {
    specifications?: string[];
    tests?: string[];
    code?: string[];
    documentation?: string[];
  };
}
