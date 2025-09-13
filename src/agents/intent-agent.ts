/**
 * Intent Agent
 * Phase 1 of ae-framework: Requirements gathering and intent analysis
 */

import type { readFileSync, writeFileSync, existsSync } from 'fs';
import type * as path from 'path';
import { SteeringLoader } from '../utils/steering-loader.js';

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

export class IntentAgent {
  private requirementCounter = 0;
  private steeringLoader: SteeringLoader;

  constructor() {
    this.steeringLoader = new SteeringLoader();
  }

  /**
   * Helper method to create a simple intent analysis request from text
   * Addresses API usability issues by providing a more intuitive interface
   */
  static createSimpleRequest(
    content: string, 
    options?: {
      sourceType?: RequirementSource['type'];
      domain?: string;
      analysisDepth?: IntentAnalysisRequest['analysisDepth'];
      outputFormat?: IntentAnalysisRequest['outputFormat'];
    }
  ): IntentAnalysisRequest {
    const sourceType = options?.sourceType || 'document';
    
    return {
      sources: [{
        type: sourceType,
        content,
        metadata: {
          priority: 'high',
          tags: ['requirement', 'analysis']
        }
      }],
      ...(options?.domain ? {
        context: {
          domain: options.domain,
          existingSystem: false,
          constraints: [],
          stakeholders: []
        }
      } : {}),
      analysisDepth: options?.analysisDepth || 'comprehensive',
      outputFormat: options?.outputFormat || 'both'
    };
  }

  /**
   * Helper method to create request from benchmark specification
   * Specifically designed for req2run-benchmark integration
   */
  static createBenchmarkRequest(spec: {
    title: string;
    description: string;
    requirements: Array<{ id: string; description: string; priority: string }>;
    constraints: any;
    metadata: {
      created_by: string;
      created_at: string;
      category: string;
      difficulty: string;
    };
  }): IntentAnalysisRequest {
    const content = `Problem: ${spec.title}

Description: ${spec.description}

Requirements:
${spec.requirements.map(r => `${r.priority}: ${r.description}`).join('\n')}

Constraints:
${JSON.stringify(spec.constraints, null, 2)}`;

    return {
      sources: [{
        type: 'document',
        content,
        metadata: {
          author: spec.metadata.created_by,
          date: new Date(spec.metadata.created_at),
          priority: 'high',
          tags: ['benchmark', 'requirement', spec.metadata.category, spec.metadata.difficulty]
        }
      }],
      context: {
        domain: spec.metadata.category,
        existingSystem: false,
        constraints: [{
          type: 'technical',
          description: 'Must use allowed packages only',
          impact: 'high',
          source: 'benchmark_spec'
        }],
        stakeholders: [
          { name: 'Developer', role: 'implementer', concerns: ['implementation quality', 'maintainability'], influenceLevel: 'high' },
          { name: 'End User', role: 'consumer', concerns: ['usability', 'functionality'], influenceLevel: 'high' }
        ]
      },
      analysisDepth: 'comprehensive',
      outputFormat: 'both'
    };
  }
  
  /**
   * Analyze requirements and extract intent
   */
  async analyzeIntent(request: IntentAnalysisRequest): Promise<IntentAnalysisResult> {
    // Load steering documents for context
    const steeringContext = await this.steeringLoader.getSteeringContext();
    
    // Extract raw requirements from sources, considering steering context
    const rawRequirements = this.extractRequirements(request.sources);
    
    // Parse and structure requirements with steering context
    const requirements = await this.parseRequirementsWithSteering(rawRequirements, request.context, steeringContext);
    
    // Generate user stories
    const userStories = this.generateUserStories(requirements);
    
    // Create use cases
    const useCases = this.generateUseCases(requirements, userStories);
    
    // Build domain model
    const domainModel = this.buildDomainModel(requirements, request.context);
    
    // Identify constraints and assumptions
    const constraints = this.identifyConstraints(rawRequirements, request.context);
    const assumptions = this.identifyAssumptions(requirements);
    
    // Risk analysis
    const risks = this.analyzeRisks(requirements, constraints);
    
    // Detect ambiguities
    const ambiguities = await this.detectAmbiguities(request.sources);
    
    // Generate suggestions
    const suggestions = this.generateSuggestions(requirements, ambiguities, risks);
    
    // Create traceability links
    const traceability = this.createTraceability(requirements);
    
    // Determine primary intent from high-priority requirements
    const primaryIntent = this.extractPrimaryIntent(requirements);
    
    return {
      requirements,
      userStories,
      useCases,
      constraints,
      assumptions,
      risks,
      domainModel,
      ambiguities,
      suggestions,
      traceability,
      primaryIntent,
    };
  }

  /**
   * Extract requirements from natural language
   */
  async extractFromNaturalLanguage(text: string): Promise<Requirement[]> {
    const requirements: Requirement[] = [];
    const sentences = text.split(/[.!?]+/);
    
    for (const sentence of sentences) {
      const requirement = this.parseNaturalLanguageRequirement(sentence);
      if (requirement) {
        requirements.push(requirement);
      }
    }
    
    return requirements;
  }

  /**
   * Generate user stories from requirements
   */
  async createUserStories(requirements: Requirement[]): Promise<UserStory[]> {
    const stories: UserStory[] = [];
    const functionalReqs = requirements.filter(r => r.type === 'functional');
    
    for (const req of functionalReqs) {
      const story = this.requirementToUserStory(req);
      stories.push(story);
    }
    
    return this.prioritizeUserStories(stories);
  }

  /**
   * Build domain model from requirements
   */
  async buildDomainModelFromRequirements(
    requirements: Requirement[],
    context?: ProjectContext
  ): Promise<DomainModel> {
    // Extract entities
    const entities = this.extractEntities(requirements);
    
    // Identify relationships
    const relationships = this.identifyRelationships(entities, requirements);
    
    // Define bounded contexts
    const boundedContexts = context ? this.defineBoundedContexts(entities, context) : [];
    
    // Identify aggregates
    const aggregates = this.identifyAggregates(entities, relationships);
    
    return {
      entities,
      relationships,
      boundedContexts,
      aggregates,
    };
  }

  /**
   * Detect and resolve ambiguities
   */
  async detectAmbiguities(sources: RequirementSource[]): Promise<Ambiguity[]> {
    const ambiguities: Ambiguity[] = [];
    const ambiguousTerms = ['maybe', 'possibly', 'should', 'might', 'could', 'sometime', 'soon'];
    const vagueTerms = ['fast', 'slow', 'big', 'small', 'good', 'bad', 'many', 'few'];
    
    for (const source of sources) {
      const text = source.content.toLowerCase();
      
      // Check for ambiguous terms
      for (const term of ambiguousTerms) {
        if (text.includes(term)) {
          ambiguities.push({
            text: term,
            type: 'vague',
            location: source.type,
            suggestion: `Replace "${term}" with specific criteria`,
            severity: 'medium',
          });
        }
      }
      
      // Check for vague terms
      for (const term of vagueTerms) {
        if (text.includes(term)) {
          ambiguities.push({
            text: term,
            type: 'vague',
            location: source.type,
            suggestion: `Define specific metrics for "${term}"`,
            severity: 'high',
          });
        }
      }
    }
    
    return ambiguities;
  }

  /**
   * Validate requirements completeness
   */
  async validateCompleteness(requirements: Requirement[]): Promise<{
    complete: boolean;
    missing: string[];
    coverage: number;
  }> {
    const requiredCategories = [
      'authentication',
      'authorization',
      'data-validation',
      'error-handling',
      'logging',
      'performance',
      'security',
      'usability',
    ];
    
    const presentCategories = new Set(requirements.map(r => r.category));
    const missing = requiredCategories.filter(cat => !presentCategories.has(cat));
    const coverage = ((requiredCategories.length - missing.length) / requiredCategories.length) * 100;
    
    return {
      complete: missing.length === 0,
      missing,
      coverage,
    };
  }

  /**
   * Generate specification templates
   */
  async generateSpecificationTemplates(requirements: Requirement[]): Promise<{
    gherkin: string[];
    openapi: object;
    asyncapi: object;
    graphql: string;
  }> {
    const gherkin = this.generateGherkinScenarios(requirements);
    const openapi = this.generateOpenAPISpec(requirements);
    const asyncapi = this.generateAsyncAPISpec(requirements);
    const graphql = this.generateGraphQLSchema(requirements);
    
    return {
      gherkin,
      openapi,
      asyncapi,
      graphql,
    };
  }

  /**
   * Prioritize requirements using MoSCoW method
   */
  async prioritizeRequirements(
    requirements: Requirement[],
    constraints: Constraint[]
  ): Promise<Requirement[]> {
    return requirements.sort((a, b) => {
      const priorityOrder = { must: 0, should: 1, could: 2, wont: 3 };
      return priorityOrder[a.priority] - priorityOrder[b.priority];
    });
  }

  /**
   * Generate acceptance criteria
   */
  async generateAcceptanceCriteria(requirement: Requirement): Promise<AcceptanceCriteria[]> {
    const criteria: AcceptanceCriteria[] = [];
    
    // Generate basic acceptance criteria
    criteria.push({
      given: `The system is in a valid state`,
      when: `The requirement "${requirement.description}" is implemented`,
      then: `The system behaves as specified`,
    });
    
    // Add specific criteria based on requirement type
    if (requirement.type === 'functional') {
      criteria.push({
        given: `A user with appropriate permissions`,
        when: `They interact with the feature`,
        then: `The expected outcome is achieved`,
      });
    }
    
    if (requirement.type === 'non-functional') {
      criteria.push({
        given: `The system is under normal load`,
        when: `The feature is accessed`,
        then: `Performance metrics are within acceptable ranges`,
      });
    }
    
    return criteria;
  }

  /**
   * Analyze stakeholder concerns
   */
  async analyzeStakeholderConcerns(
    stakeholders: Stakeholder[],
    requirements: Requirement[]
  ): Promise<{
    addressed: Map<string, string[]>;
    unaddressed: Map<string, string[]>;
    conflicts: Array<{ stakeholder1: string; stakeholder2: string; issue: string }>;
  }> {
    const addressed = new Map<string, string[]>();
    const unaddressed = new Map<string, string[]>();
    const conflicts: Array<{ stakeholder1: string; stakeholder2: string; issue: string }> = [];
    
    for (const stakeholder of stakeholders) {
      const addressedConcerns: string[] = [];
      const unaddressedConcerns: string[] = [];
      
      for (const concern of stakeholder.concerns) {
        const isAddressed = requirements.some(req => 
          req.description.toLowerCase().includes(concern.toLowerCase())
        );
        
        if (isAddressed) {
          addressedConcerns.push(concern);
        } else {
          unaddressedConcerns.push(concern);
        }
      }
      
      addressed.set(stakeholder.name, addressedConcerns);
      unaddressed.set(stakeholder.name, unaddressedConcerns);
    }
    
    // Check for conflicts between stakeholders
    for (let i = 0; i < stakeholders.length; i++) {
      for (let j = i + 1; j < stakeholders.length; j++) {
        const conflictingConcerns = this.findConflicts(
          stakeholders[i]?.concerns || [],
          stakeholders[j]?.concerns || []
        );
        
        for (const issue of conflictingConcerns) {
          conflicts.push({
            stakeholder1: stakeholders[i]?.name || 'Unknown',
            stakeholder2: stakeholders[j]?.name || 'Unknown',
            issue,
          });
        }
      }
    }
    
    return { addressed, unaddressed, conflicts };
  }

  // Private helper methods

  private extractRequirements(sources: RequirementSource[]): string[] {
    const requirements: string[] = [];
    
    for (const source of sources) {
      const extracted = this.extractFromSource(source);
      requirements.push(...extracted);
    }
    
    return requirements;
  }

  private extractFromSource(source: RequirementSource): string[] {
    switch (source.type) {
      case 'text':
        return source.content.split('\n').filter(line => line.trim());
      case 'document':
        return this.parseDocument(source.content);
      case 'conversation':
        return this.extractFromConversation(source.content);
      case 'issue':
        return this.parseIssue(source.content);
      case 'email':
        return this.extractFromEmail(source.content);
      case 'diagram':
        return this.extractFromDiagram(source.content);
      default:
        return [source.content];
    }
  }

  private parseDocument(content: string): string[] {
    // Extract requirements from structured documents
    const lines = content.split('\n');
    const requirements: string[] = [];
    
    for (const line of lines) {
      const trimmedLine = line.trim();
      
      // Match various requirement patterns:
      // - Numbered: "1. requirement", "1) requirement"  
      // - Bullet points: "- requirement", "* requirement"
      // - Priority levels: "MUST: requirement", "SHOULD: requirement", "MAY: requirement"
      // - Keywords: "The system must/should/shall"
      if (trimmedLine.match(/^(\d+[\.\)]\s+|[\-\*]\s+|(MUST|SHOULD|MAY|SHALL):\s*|.*(must|should|shall|will)\s+)/i)) {
        let cleanRequirement = trimmedLine
          .replace(/^(\d+[\.\)]\s+|[\-\*]\s+|(MUST|SHOULD|MAY|SHALL):\s*)/i, '')
          .trim();
        
        // If the requirement is still meaningful after cleaning, add it
        if (cleanRequirement.length > 10) {
          requirements.push(cleanRequirement);
        }
      }
      
      // Also extract lines that contain clear requirement indicators
      else if (trimmedLine.match(/(requirement|feature|capability|function).*:/i) && trimmedLine.length > 15) {
        requirements.push(trimmedLine);
      }
    }
    
    return requirements;
  }

  private extractFromConversation(content: string): string[] {
    // Extract requirements from conversation transcripts
    const requirements: string[] = [];
    const patterns = [
      /I need (.+)/gi,
      /We want (.+)/gi,
      /The system should (.+)/gi,
      /Users must be able to (.+)/gi,
    ];
    
    for (const pattern of patterns) {
      let match;
      pattern.lastIndex = 0; // Reset regex state
      while ((match = pattern.exec(content)) !== null) {
        if (match[1]) {
          requirements.push(match[1]);
        }
        // All patterns are global, so continue until no more matches
      }
    }
    
    return requirements;
  }

  private parseIssue(content: string): string[] {
    // Parse GitHub/Jira style issues
    const requirements: string[] = [];
    const sections = content.split(/#+\s+/);
    
    for (const section of sections) {
      if (section.toLowerCase().includes('requirement') || 
          section.toLowerCase().includes('acceptance')) {
        requirements.push(section.trim());
      }
    }
    
    return requirements;
  }

  private extractFromEmail(content: string): string[] {
    // Extract requirements from email content
    return this.extractFromConversation(content);
  }

  private extractFromDiagram(content: string): string[] {
    // Extract requirements from diagram descriptions
    return [content];
  }

  private parseRequirements(
    raw: string[],
    context?: ProjectContext
  ): Requirement[] {
    return raw.map((text, index) => ({
      id: `REQ-${String(index + 1).padStart(3, '0')}`,
      type: this.determineRequirementType(text),
      category: this.determineCategory(text),
      description: text,
      priority: this.determinePriority(text),
      acceptance: [],
      source: 'extracted',
      status: 'draft',
    }));
  }

  private determineRequirementType(text: string): Requirement['type'] {
    const lowerText = text.toLowerCase();
    
    // Non-functional requirements (performance, security, quality attributes)
    if (lowerText.includes('performance') || 
        lowerText.includes('security') || 
        lowerText.includes('scalability') ||
        lowerText.includes('usability') ||
        lowerText.includes('reliability') ||
        lowerText.includes('availability') ||
        lowerText.includes('response time') ||
        lowerText.includes('throughput')) {
      return 'non-functional';
    }
    
    // Business requirements (business rules, policies, objectives)
    if (lowerText.includes('business') || 
        lowerText.includes('revenue') || 
        lowerText.includes('customer') ||
        lowerText.includes('policy') ||
        lowerText.includes('compliance') ||
        lowerText.includes('regulation')) {
      return 'business';
    }
    
    // Technical requirements (infrastructure, APIs, technical constraints)
    if (lowerText.includes('api') || 
        lowerText.includes('database') || 
        lowerText.includes('integration') ||
        lowerText.includes('platform') ||
        lowerText.includes('architecture') ||
        lowerText.includes('framework') ||
        lowerText.includes('technology')) {
      return 'technical';
    }
    
    // Functional requirements (what the system should do)
    return 'functional';
  }

  private determineCategory(text: string): string {
    const lowerText = text.toLowerCase();
    
    if (lowerText.includes('auth')) return 'authentication';
    if (lowerText.includes('security')) return 'security';
    if (lowerText.includes('performance')) return 'performance';
    if (lowerText.includes('data')) return 'data-management';
    if (lowerText.includes('ui') || lowerText.includes('user interface')) return 'ui';
    if (lowerText.includes('api')) return 'api';
    
    return 'general';
  }

  private determinePriority(text: string): Requirement['priority'] {
    const lowerText = text.toLowerCase();
    
    if (lowerText.includes('must') || lowerText.includes('critical')) return 'must';
    if (lowerText.includes('should') || lowerText.includes('important')) return 'should';
    if (lowerText.includes('could') || lowerText.includes('nice to have')) return 'could';
    if (lowerText.includes('wont') || lowerText.includes('future')) return 'wont';
    
    return 'should';
  }

  private generateUserStories(requirements: Requirement[]): UserStory[] {
    return requirements
      .filter(req => req.type === 'functional')
      .map((req, index) => {
        // Generate more meaningful user story titles
        const title = this.generateUserStoryTitle(req.description);
        const narrative = this.generateUserStoryNarrative(req.description);
        
        return {
          id: `US-${String(index + 1).padStart(3, '0')}`,
          title,
          narrative,
          acceptance: req.acceptance,
          priority: req.priority === 'must' ? 'high' : 
                    req.priority === 'should' ? 'medium' : 'low',
          requirements: [req.id],
        };
      });
  }

  private generateUserStoryTitle(description: string): string {
    // Create meaningful titles from requirements
    const words = description.split(' ');
    if (words.length > 8) {
      return words.slice(0, 8).join(' ') + '...';
    }
    return description.length > 50 ? description.substring(0, 47) + '...' : description;
  }

  private generateUserStoryNarrative(description: string): UserStory['narrative'] {
    // Extract action words and objects to create better narratives
    const lowerDesc = description.toLowerCase();
    
    // Determine user type based on context
    let userType = 'user';
    if (lowerDesc.includes('developer') || lowerDesc.includes('admin')) {
      userType = 'developer';
    } else if (lowerDesc.includes('system') || lowerDesc.includes('automated')) {
      userType = 'system operator';
    }
    
    // Extract the action/want from description
    let want = description;
    if (description.includes('should') || description.includes('must') || description.includes('shall')) {
      want = description.replace(/(should|must|shall|will)\s+/gi, '').trim();
    }
    
    // Generate meaningful "so that" clause based on requirement type
    let soThat = 'I can accomplish my task efficiently';
    if (lowerDesc.includes('convert') || lowerDesc.includes('transform')) {
      soThat = 'I can work with data in different formats';
    } else if (lowerDesc.includes('validate') || lowerDesc.includes('check')) {
      soThat = 'I can ensure data integrity';
    } else if (lowerDesc.includes('process') || lowerDesc.includes('handle')) {
      soThat = 'I can manage my data effectively';
    } else if (lowerDesc.includes('output') || lowerDesc.includes('display')) {
      soThat = 'I can understand the results clearly';
    }
    
    return {
      asA: userType,
      iWant: want,
      soThat,
    };
  }

  private generateUseCases(
    requirements: Requirement[],
    userStories: UserStory[]
  ): UseCase[] {
    return userStories.map((story, index) => ({
      id: `UC-${String(index + 1).padStart(3, '0')}`,
      name: story.title,
      actors: ['User', 'System'],
      preconditions: ['User is authenticated', 'System is available'],
      mainFlow: [
        {
          number: 1,
          actor: 'User',
          action: 'Initiates action',
          system: 'Processes request',
        },
      ],
      alternativeFlows: [],
      postconditions: ['Action completed successfully'],
      exceptions: [],
    }));
  }

  private buildDomainModel(
    requirements: Requirement[],
    context?: ProjectContext
  ): DomainModel {
    const entities = this.extractEntities(requirements);
    const relationships = this.identifyRelationships(entities, requirements);
    const boundedContexts = context ? 
      this.defineBoundedContexts(entities, context) : [];
    const aggregates = this.identifyAggregates(entities, relationships);
    
    return {
      entities,
      relationships,
      boundedContexts,
      aggregates,
    };
  }

  private extractEntities(requirements: Requirement[]): Entity[] {
    const entities: Entity[] = [];
    const entityNames = new Set<string>();
    
    for (const req of requirements) {
      // Simple noun extraction (would be more sophisticated in practice)
      const nouns = req.description.match(/\b[A-Z][a-z]+\b/g) || [];
      
      for (const noun of nouns) {
        if (!entityNames.has(noun)) {
          entityNames.add(noun);
          entities.push({
            name: noun,
            attributes: [],
            behaviors: [],
            invariants: [],
          });
        }
      }
    }
    
    return entities;
  }

  private identifyRelationships(
    entities: Entity[],
    requirements: Requirement[]
  ): Relationship[] {
    const relationships: Relationship[] = [];
    
    // Simple relationship detection
    for (let i = 0; i < entities.length; i++) {
      for (let j = i + 1; j < entities.length; j++) {
        relationships.push({
          from: entities[i]?.name || `entity_${i}`,
          to: entities[j]?.name || `entity_${j}`,
          type: 'references',
          cardinality: '1-n',
        });
      }
    }
    
    return relationships;
  }

  private defineBoundedContexts(
    entities: Entity[],
    context: ProjectContext
  ): BoundedContext[] {
    return [{
      name: context.domain,
      entities: entities.map(e => e.name),
      ubiquitousLanguage: context.glossary || [],
    }];
  }

  private identifyAggregates(
    entities: Entity[],
    relationships: Relationship[]
  ): Aggregate[] {
    // Simple aggregate identification
    return entities
      .filter(e => relationships.some(r => r.from === e.name))
      .map(e => ({
        root: e.name,
        entities: relationships
          .filter(r => r.from === e.name)
          .map(r => r.to),
        invariants: [],
      }));
  }

  private identifyConstraints(
    raw: string[],
    context?: ProjectContext
  ): Constraint[] {
    const constraints = context?.constraints || [];
    
    // Extract constraints from requirements
    for (const text of raw) {
      if (text.toLowerCase().includes('constraint') || 
          text.toLowerCase().includes('limitation')) {
        constraints.push({
          type: 'technical',
          description: text,
          impact: 'medium',
          source: 'requirements_analysis'
        });
      }
    }
    
    return constraints;
  }

  private identifyAssumptions(requirements: Requirement[]): Assumption[] {
    return requirements
      .filter(req => req.description.toLowerCase().includes('assume'))
      .map((req, index) => ({
        id: `ASM-${String(index + 1).padStart(3, '0')}`,
        description: req.description,
        impact: 'medium',
        validation: 'To be validated',
      }));
  }

  private analyzeRisks(
    requirements: Requirement[],
    constraints: Constraint[]
  ): Risk[] {
    const risks: Risk[] = [];
    
    // Technical risks
    if (requirements.some(r => r.category === 'performance')) {
      risks.push({
        id: 'RISK-001',
        description: 'Performance requirements may not be met',
        probability: 'medium',
        impact: 'high',
        mitigation: 'Implement performance testing early',
      });
    }
    
    // Security risks
    if (requirements.some(r => r.category === 'security')) {
      risks.push({
        id: 'RISK-002',
        description: 'Security vulnerabilities may be introduced',
        probability: 'medium',
        impact: 'high',
        mitigation: 'Implement security testing and code reviews',
      });
    }
    
    return risks;
  }

  private generateSuggestions(
    requirements: Requirement[],
    ambiguities: Ambiguity[],
    risks: Risk[]
  ): string[] {
    const suggestions: string[] = [];
    
    if (ambiguities.length > 0) {
      suggestions.push(`Resolve ${ambiguities.length} ambiguities in requirements`);
    }
    
    if (risks.filter(r => r.impact === 'high').length > 0) {
      suggestions.push('Address high-impact risks before implementation');
    }
    
    const categories = new Set(requirements.map(r => r.category));
    if (!categories.has('security')) {
      suggestions.push('Add security requirements');
    }
    
    if (!categories.has('performance')) {
      suggestions.push('Define performance requirements');
    }
    
    return suggestions;
  }

  private createTraceability(requirements: Requirement[]): RequirementTrace[] {
    return requirements.map(req => ({
      requirementId: req.id,
      linkedTo: {
        specifications: [],
        tests: [],
        code: [],
        documentation: [],
      },
    }));
  }

  private parseNaturalLanguageRequirement(sentence: string): Requirement | null {
    if (!sentence.trim()) return null;
    
    return {
      id: `REQ-${++this.requirementCounter}-${Date.now().toString(36)}`,
      type: this.determineRequirementType(sentence),
      category: this.determineCategory(sentence),
      description: sentence.trim(),
      priority: this.determinePriority(sentence),
      acceptance: [],
      source: 'natural-language',
      status: 'draft',
    };
  }

  private requirementToUserStory(req: Requirement): UserStory {
    return {
      id: `US-${req.id}`,
      title: req.description.substring(0, 50),
      narrative: {
        asA: 'user',
        iWant: req.description,
        soThat: req.rationale || 'I can achieve my goals',
      },
      acceptance: req.acceptance,
      priority: req.priority === 'must' ? 'high' : 
                req.priority === 'should' ? 'medium' : 'low',
      requirements: [req.id],
    };
  }

  private prioritizeUserStories(stories: UserStory[]): UserStory[] {
    return stories.sort((a, b) => {
      const priorityOrder = { high: 0, medium: 1, low: 2 };
      return priorityOrder[a.priority] - priorityOrder[b.priority];
    });
  }

  private generateGherkinScenarios(requirements: Requirement[]): string[] {
    return requirements.map(req => 
      `Feature: ${req.description}\n` +
      `  Scenario: Implement ${req.id}\n` +
      `    Given the system is ready\n` +
      `    When the requirement is implemented\n` +
      `    Then the system meets the requirement\n`
    );
  }

  private generateOpenAPISpec(requirements: Requirement[]): object {
    return {
      openapi: '3.0.0',
      info: {
        title: 'Generated API',
        version: '1.0.0',
      },
      paths: {},
    };
  }

  private generateAsyncAPISpec(requirements: Requirement[]): object {
    return {
      asyncapi: '2.0.0',
      info: {
        title: 'Generated Async API',
        version: '1.0.0',
      },
      channels: {},
    };
  }

  private generateGraphQLSchema(requirements: Requirement[]): string {
    return `type Query {\n  # Generated from requirements\n}\n`;
  }

  private findConflicts(concerns1: string[], concerns2: string[]): string[] {
    const conflicts: string[] = [];
    
    // Simple conflict detection
    for (const c1 of concerns1) {
      for (const c2 of concerns2) {
        if (this.areConflicting(c1, c2)) {
          conflicts.push(`${c1} conflicts with ${c2}`);
        }
      }
    }
    
    return conflicts;
  }

  private areConflicting(concern1: string, concern2: string): boolean {
    // Simple heuristic for conflict detection
    const opposites = [
      ['fast', 'secure'],
      ['simple', 'comprehensive'],
      ['flexible', 'strict'],
    ];
    
    for (const [a, b] of opposites) {
      if (a && b && concern1 && concern2 &&
          ((concern1.includes(a) && concern2.includes(b)) ||
          (concern1.includes(b) && concern2.includes(a)))) {
        return true;
      }
    }
    
    return false;
  }

  /**
   * Parse requirements with steering document context
   */
  private async parseRequirementsWithSteering(
    raw: string[],
    context: ProjectContext | undefined,
    steeringContext: string
  ): Promise<Requirement[]> {
    const requirements = this.parseRequirements(raw, context);
    
    // Enhance requirements based on steering documents
    const steeringDocs = await this.steeringLoader.loadAllDocuments();
    
    // If product steering exists, enhance with product context
    if (steeringDocs['product']) {
      requirements.forEach(req => {
        // Add product context to requirements (case-insensitive check)
        if (!req.rationale && steeringDocs['product']?.toLowerCase().includes('vision')) {
          req.rationale = 'Aligns with product vision';
        }
      });
    }
    
    // If architecture steering exists, categorize technical requirements
    if (steeringDocs['architecture']) {
      const archKeywords = ['api', 'database', 'microservice', 'architecture', 'integration', 'infrastructure'];
      requirements.forEach(req => {
        if (req.type === 'technical') {
          // More flexible matching using keywords
          const reqLower = req.description.toLowerCase();
          const archLower = steeringDocs['architecture']?.toLowerCase() || '';
          
          // Check if requirement contains architecture keywords or if architecture doc mentions the requirement
          const isArchRelated = archKeywords.some(keyword => reqLower.includes(keyword)) ||
                               reqLower.split(' ').some(word => archLower.includes(word));
          
          if (isArchRelated) {
            req.category = 'architecture';
          }
        }
      });
    }
    
    // If standards steering exists, apply priority based on standards
    if (steeringDocs['standards']) {
      // Extract mandatory standards with more sophisticated parsing
      const standardsLower = steeringDocs['standards'].toLowerCase();
      const mandatoryPatterns = [
        /must\s+(?:have|implement|follow|use)\s+(\w+)/g,
        /required:\s*([^,\n]+)/g,
        /mandatory:\s*([^,\n]+)/g
      ];
      
      const mandatoryStandards: string[] = [];
      mandatoryPatterns.forEach(pattern => {
        let match;
        pattern.lastIndex = 0; // Reset regex state
        while ((match = pattern.exec(standardsLower)) !== null) {
          if (match[1]) {
            mandatoryStandards.push(match[1].trim());
          }
          // All patterns are global, so continue until no more matches
        }
      });
      
      requirements.forEach(req => {
        const reqLower = req.description.toLowerCase();
        
        // Check if requirement relates to any mandatory standard
        const relatesToMandatory = mandatoryStandards.some(standard => 
          reqLower.includes(standard) || reqLower.includes('standard')
        );
        
        // Also check for explicit priority keywords in standards doc
        if (relatesToMandatory || 
            (standardsLower.includes('must') && reqLower.includes('standard'))) {
          req.priority = 'must';
        }
      });
    }
    
    return requirements;
  }

  /**
   * Get steering-aware suggestions
   */
  async getSteeringAwareSuggestions(): Promise<string[]> {
    const suggestions: string[] = [];
    const hasSteeringDocs = await this.steeringLoader.hasSteeringDocuments();
    
    if (!hasSteeringDocs) {
      suggestions.push('Initialize steering documents for better context (.ae/steering/)');
      suggestions.push('Define product vision in .ae/steering/product.md');
      suggestions.push('Document architecture decisions in .ae/steering/architecture.md');
      suggestions.push('Establish coding standards in .ae/steering/standards.md');
    } else {
      const docs = await this.steeringLoader.loadAllDocuments();
      
      if (!docs['product']) {
        suggestions.push('Create product steering document for clearer vision');
      }
      
      if (!docs['architecture']) {
        suggestions.push('Create architecture steering document for technical consistency');
      }
      
      if (!docs['standards']) {
        suggestions.push('Create standards steering document for code quality');
      }
    }
    
    return suggestions;
  }

  /**
   * Extract primary intent from requirements
   */
  private extractPrimaryIntent(requirements: Requirement[]): string {
    // Find the highest priority requirement
    const mustHaveReqs = requirements.filter(req => req.priority === 'must');
    if (mustHaveReqs.length > 0) {
      return mustHaveReqs[0]!.description;
    }

    // Fall back to first should-have requirement
    const shouldHaveReqs = requirements.filter(req => req.priority === 'should');
    if (shouldHaveReqs.length > 0) {
      return shouldHaveReqs[0]!.description;
    }

    // Fall back to any functional requirement
    const functionalReqs = requirements.filter(req => req.type === 'functional');
    if (functionalReqs.length > 0) {
      return functionalReqs[0]!.description;
    }

    // Ultimate fallback
    return requirements.length > 0 ? requirements[0]!.description : 'Define system requirements and functionality';
  }
}
