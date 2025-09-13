/**
 * Domain Modeling Task Adapter for Claude Code
 * 
 * This adapter integrates Phase 5 (Domain Modeling) processing with Claude Code's
 * Task tool, enabling seamless domain analysis, entity modeling, and
 * architectural design workflows.
 */

import { FormalAgent } from './formal-agent.js';
import type { FormalAgentConfig } from './formal-agent.js';
import type { TaskRequest, TaskResponse } from './task-types.js';

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

export class DomainModelingTaskAdapter {
  private agent: FormalAgent;

  constructor() {
    const config: FormalAgentConfig = {
      outputFormat: 'openapi',
      validationLevel: 'comprehensive',
      generateDiagrams: true,
      enableModelChecking: true,
    };

    this.agent = new FormalAgent(config);
  }

  /**
   * Main handler for Domain Modeling tasks from Claude Code
   */
  async handleDomainModelingTask(request: TaskRequest): Promise<TaskResponse> {
    const taskType = this.classifyTask(request.description, request.prompt);
    
    switch (taskType) {
      case 'analyze-domain':
        return this.handleDomainAnalysis(request);
      
      case 'identify-entities':
        return this.handleEntityIdentification(request);
      
      case 'model-aggregates':
        return this.handleAggregateModeling(request);
      
      case 'define-bounded-contexts':
        return this.handleBoundedContextDefinition(request);
      
      case 'extract-business-rules':
        return this.handleBusinessRuleExtraction(request);
      
      case 'create-ubiquitous-language':
        return this.handleUbiquitousLanguageCreation(request);
      
      case 'design-domain-services':
        return this.handleDomainServiceDesign(request);
      
      case 'validate-domain-model':
        return this.handleDomainModelValidation(request);
      
      default:
        return this.handleGenericDomainModeling(request);
    }
  }

  /**
   * Proactive domain modeling guidance for Claude Code
   */
  async provideProactiveGuidance(context: {
    recentFiles: string[];
    recentActions: string[];
    userIntent: string;
  }): Promise<{
    shouldIntervene: boolean;
    intervention: {
      type: 'warning' | 'suggestion' | 'block';
      message: string;
      recommendedActions: string[];
    };
  }> {
    const analysis = await this.analyzeRecentActivity(context);
    
    if (analysis.hasIncompleteModeling) {
      return {
        shouldIntervene: true,
        intervention: {
          type: 'warning',
          message: 'Domain model appears incomplete - key entities or relationships may be missing',
          recommendedActions: analysis.completionActions,
        },
      };
    }

    if (analysis.hasModelingInconsistencies) {
      return {
        shouldIntervene: true,
        intervention: {
          type: 'suggestion',
          message: 'Domain model inconsistencies detected - review entity relationships and business rules',
          recommendedActions: analysis.consistencyActions,
        },
      };
    }

    if (analysis.shouldRefineModel) {
      return {
        shouldIntervene: true,
        intervention: {
          type: 'suggestion',
          message: 'Consider refining domain model based on recent requirements changes',
          recommendedActions: analysis.refinementActions,
        },
      };
    }

    return {
      shouldIntervene: false,
      intervention: {
        type: 'suggestion',
        message: 'Domain model looks comprehensive and consistent',
        recommendedActions: [],
      },
    };
  }

  private async handleDomainAnalysis(request: TaskRequest): Promise<TaskResponse> {
    const domainInput = this.extractDomainInput(request.prompt);
    const analysis = await this.analyzeDomain(domainInput);
    
    return {
      summary: `Domain Analysis Complete - ${analysis.entities.length} entities, ${analysis.boundedContexts.length} bounded contexts identified`,
      analysis: `
# Domain Analysis Report

**Identified Entities**: ${analysis.entities.length}
**Bounded Contexts**: ${analysis.boundedContexts.length}
**Business Rules**: ${analysis.businessRules.length}
**Domain Services**: ${analysis.domainServices.length}

## Core Domain Entities
${analysis.coreEntities.map((entity: any) => 
  `• **${entity.name}** (${entity.type}): ${entity.description}`
).join('\n')}

## Bounded Contexts Overview
${analysis.boundedContexts.map((context: any) => 
  `• **${context.name}**: ${context.description} (${context.entities.length} entities)`
).join('\n')}

## Key Business Rules
${analysis.keyBusinessRules.map((rule: any) => 
  `• **${rule.name}**: ${rule.description}`
).join('\n')}

## Domain Complexity Analysis
- **High Complexity Areas**: ${analysis.complexityAnalysis.high.join(', ')}
- **Medium Complexity Areas**: ${analysis.complexityAnalysis.medium.join(', ')}
- **Simple Areas**: ${analysis.complexityAnalysis.simple.join(', ')}
      `.trim(),
      recommendations: [
        'Focus on high-complexity areas for detailed modeling',
        'Define clear bounded context boundaries',
        'Establish ubiquitous language for key terms',
        'Validate business rules with domain experts',
      ],
      nextActions: [
        'Create detailed entity models for core domain',
        'Define aggregate boundaries',
        'Document ubiquitous language terms',
        'Design domain service interfaces',
      ],
      warnings: analysis.complexityWarnings.map((warning: any) => warning.description),
      shouldBlockProgress: analysis.criticalGaps.length > 0,
    };
  }

  private async handleEntityIdentification(request: TaskRequest): Promise<TaskResponse> {
    const input = this.extractEntityInput(request.prompt);
    const entities = await this.identifyEntities(input);
    
    return {
      summary: `Entity Identification Complete - ${entities.entities.length} entities identified`,
      analysis: `
# Entity Identification Report

**Total Entities**: ${entities.entities.length}
**Aggregate Roots**: ${entities.aggregateRoots.length}
**Value Objects**: ${entities.valueObjects.length}
**Domain Services**: ${entities.domainServices.length}

## Entity Classification
${entities.entities.map((entity: any) => 
  `• **${entity.name}** (${entity.type}): ${entity.description}`
).join('\n')}

## Entity Relationships
${entities.relationships.map((rel: any) => 
  `• ${rel.from} ${rel.type} ${rel.to} (${rel.cardinality})`
).join('\n')}

## Business Rule Coverage
${entities.businessRuleCoverage.map((coverage: any) => 
  `• **${coverage.entity}**: ${coverage.rulesCount} business rules`
).join('\n')}
      `.trim(),
      recommendations: [
        'Review entity classifications with domain experts',
        'Validate entity relationships and cardinalities',
        'Ensure all business rules are captured',
        'Consider aggregate boundaries carefully',
      ],
      nextActions: [
        'Define entity attributes and methods',
        'Establish entity invariants',
        'Design aggregate root interfaces',
        'Validate entity model with use cases',
      ],
      warnings: entities.warnings.map((warning: any) => warning.description),
      shouldBlockProgress: false,
    };
  }

  private async handleAggregateModeling(request: TaskRequest): Promise<TaskResponse> {
    const input = this.extractAggregateInput(request.prompt);
    const aggregates = await this.modelAggregates(input);
    
    return {
      summary: `Aggregate Modeling Complete - ${aggregates.aggregates.length} aggregates defined`,
      analysis: `
# Aggregate Modeling Report

**Total Aggregates**: ${aggregates.aggregates.length}

## Aggregate Details
${aggregates.aggregates.map((agg: any) => `
### ${agg.name}
- **Description**: ${agg.description}
- **Entities**: ${agg.entities.join(', ')}
- **Value Objects**: ${agg.valueObjects.join(', ')}
- **Business Rules**: ${agg.businessRules.length}
- **Invariants**: ${agg.invariants.length}
`).join('\n')}

## Aggregate Boundaries Analysis
${aggregates.boundaryAnalysis.map((analysis: any) => 
  `• **${analysis.aggregate}**: ${analysis.boundaryStrength} boundary strength (${analysis.cohesion}% cohesion)`
).join('\n')}

## Cross-Aggregate Dependencies
${aggregates.dependencies.map((dep: any) => 
  `• ${dep.from} → ${dep.to} (${dep.type}: ${dep.reason})`
).join('\n')}
      `.trim(),
      recommendations: [
        'Review aggregate boundaries for optimal cohesion',
        'Minimize cross-aggregate dependencies',
        'Ensure each aggregate has clear business purpose',
        'Validate aggregate invariants',
      ],
      nextActions: [
        'Design aggregate command interfaces',
        'Define aggregate event publishing',
        'Create aggregate repositories',
        'Implement aggregate business rules',
      ],
      warnings: aggregates.boundaryWarnings.map((warning: any) => warning.description),
      shouldBlockProgress: aggregates.criticalIssues.length > 0,
    };
  }

  private async handleBoundedContextDefinition(request: TaskRequest): Promise<TaskResponse> {
    const input = this.extractContextInput(request.prompt);
    const contexts = await this.defineBoundedContexts(input);
    
    return {
      summary: `Bounded Context Definition Complete - ${contexts.contexts.length} contexts defined`,
      analysis: `
# Bounded Context Analysis

**Total Contexts**: ${contexts.contexts.length}

## Context Definitions
${contexts.contexts.map((context: any) => `
### ${context.name}
- **Description**: ${context.description}
- **Entities**: ${context.entities.length}
- **Services**: ${context.services.length}
- **Responsibilities**: ${context.responsibilities.join(', ')}
`).join('\n')}

## Context Relationships
${contexts.relationships.map((rel: any) => 
  `• **${rel.upstream}** → **${rel.downstream}** (${rel.type})`
).join('\n')}

## Integration Patterns
${contexts.integrationPatterns.map((pattern: any) => 
  `• **${pattern.contexts.join(' ↔ ')}**: ${pattern.pattern} (${pattern.description})`
).join('\n')}
      `.trim(),
      recommendations: [
        'Validate context boundaries with team structure',
        'Design clear context integration contracts',
        'Establish anti-corruption layers where needed',
        'Document context responsibilities clearly',
      ],
      nextActions: [
        'Define context APIs and contracts',
        'Design inter-context communication',
        'Implement context integration patterns',
        'Create context deployment strategies',
      ],
      warnings: contexts.integrationRisks.map((risk: any) => risk.description),
      shouldBlockProgress: false,
    };
  }

  private async handleBusinessRuleExtraction(request: TaskRequest): Promise<TaskResponse> {
    const input = this.extractBusinessRuleInput(request.prompt);
    const rules = await this.extractBusinessRules(input);
    
    return {
      summary: `Business Rule Extraction Complete - ${rules.rules.length} rules identified`,
      analysis: `
# Business Rules Analysis

**Total Rules**: ${rules.rules.length}
**Constraint Rules**: ${rules.rules.filter((r: any) => r.type === 'constraint').length}
**Derivation Rules**: ${rules.rules.filter((r: any) => r.type === 'derivation').length}
**Action Enablers**: ${rules.rules.filter((r: any) => r.type === 'action_enabler').length}

## High Priority Rules
${rules.rules
  .filter((r: any) => r.priority === 'high')
  .map((rule: any) => `• **${rule.name}**: ${rule.description}`)
  .join('\n')}

## Rule Complexity Analysis
${rules.complexityAnalysis.map((analysis: any) => 
  `• **${analysis.rule}**: ${analysis.complexity} complexity (${analysis.dependencies} dependencies)`
).join('\n')}

## Entity-Rule Mapping
${rules.entityMapping.map((mapping: any) => 
  `• **${mapping.entity}**: ${mapping.rules.length} rules`
).join('\n')}
      `.trim(),
      recommendations: [
        'Prioritize implementation of high-priority rules',
        'Break down complex rules into simpler components',
        'Validate rules with business stakeholders',
        'Ensure rules are testable and verifiable',
      ],
      nextActions: [
        'Implement business rule validation',
        'Create rule execution framework',
        'Design rule testing strategies',
        'Document rule change procedures',
      ],
      warnings: rules.conflictingRules.map((conflict: any) => conflict.description),
      shouldBlockProgress: rules.conflictingRules.length > 0,
    };
  }

  private async handleUbiquitousLanguageCreation(request: TaskRequest): Promise<TaskResponse> {
    const input = this.extractLanguageInput(request.prompt);
    const language = await this.createUbiquitousLanguage(input);
    
    return {
      summary: `Ubiquitous Language Creation Complete - ${language.terms.length} terms defined`,
      analysis: `
# Ubiquitous Language Dictionary

**Total Terms**: ${language.terms.length}
**Core Domain Terms**: ${language.coreTerms.length}
**Supporting Terms**: ${language.supportingTerms.length}

## Core Domain Terms
${language.coreTerms.map((term: any) => 
  `• **${term.term}**: ${term.definition} (Context: ${term.context})`
).join('\n')}

## Term Relationships
${language.termRelationships.map((rel: any) => 
  `• **${rel.term1}** ${rel.relationship} **${rel.term2}**`
).join('\n')}

## Ambiguous Terms
${language.ambiguousTerms.map((term: any) => 
  `• **${term.term}**: Multiple definitions found - requires clarification`
).join('\n')}
      `.trim(),
      recommendations: [
        'Resolve ambiguous terms with domain experts',
        'Ensure consistent term usage across contexts',
        'Create term validation guidelines',
        'Establish term evolution procedures',
      ],
      nextActions: [
        'Create language validation tools',
        'Implement term consistency checking',
        'Design language evolution process',
        'Create team communication guidelines',
      ],
      warnings: language.ambiguousTerms.map((term: any) => `Ambiguous term: ${term.term}`),
      shouldBlockProgress: false,
    };
  }

  private async handleDomainServiceDesign(request: TaskRequest): Promise<TaskResponse> {
    const input = this.extractServiceInput(request.prompt);
    const services = await this.designDomainServices(input);
    
    return {
      summary: `Domain Service Design Complete - ${services.services.length} services designed`,
      analysis: `
# Domain Services Design

**Total Services**: ${services.services.length}

## Service Definitions
${services.services.map((service: any) => `
### ${service.name}
- **Description**: ${service.description}
- **Operations**: ${service.operations.length}
- **Dependencies**: ${service.dependencies.join(', ')}
`).join('\n')}

## Service Dependencies
${services.dependencyAnalysis.map((dep: any) => 
  `• **${dep.service}**: ${dep.dependencies.length} dependencies (${dep.coupling} coupling)`
).join('\n')}

## Service Cohesion Analysis
${services.cohesionAnalysis.map((analysis: any) => 
  `• **${analysis.service}**: ${analysis.cohesion}% cohesion (${analysis.responsibilities} responsibilities)`
).join('\n')}
      `.trim(),
      recommendations: [
        'Minimize service dependencies',
        'Ensure high cohesion within services',
        'Design clear service interfaces',
        'Consider service granularity carefully',
      ],
      nextActions: [
        'Implement service interfaces',
        'Design service testing strategies',
        'Create service documentation',
        'Plan service deployment architecture',
      ],
      warnings: services.designIssues.map((issue: any) => issue.description),
      shouldBlockProgress: false,
    };
  }

  private async handleDomainModelValidation(request: TaskRequest): Promise<TaskResponse> {
    const input = this.extractModelInput(request.prompt);
    const validation = await this.validateDomainModel(input);
    
    return {
      summary: `Domain Model Validation Complete - ${validation.score}% valid`,
      analysis: `
# Domain Model Validation Report

**Overall Validation Score**: ${validation.score}%
**Entity Validation**: ${validation.entityValidation}%
**Relationship Validation**: ${validation.relationshipValidation}%
**Business Rule Validation**: ${validation.businessRuleValidation}%

## Validation Issues
${validation.issues.map((issue: any) => 
  `• **${issue.severity}**: ${issue.description} (${issue.category})`
).join('\n')}

## Model Completeness
- **Entities**: ${validation.completeness.entities}%
- **Relationships**: ${validation.completeness.relationships}%
- **Business Rules**: ${validation.completeness.businessRules}%
- **Bounded Contexts**: ${validation.completeness.boundedContexts}%

## Consistency Checks
${validation.consistencyChecks.map((check: any) => 
  `• **${check.category}**: ${check.status} (${check.issues} issues)`
).join('\n')}
      `.trim(),
      recommendations: validation.recommendations,
      nextActions: [
        'Address critical validation issues',
        'Improve model completeness',
        'Validate model with stakeholders',
        'Create model evolution strategy',
      ],
      warnings: validation.criticalIssues.map((issue: any) => issue.description),
      shouldBlockProgress: validation.criticalIssues.length > 0,
    };
  }

  private async handleGenericDomainModeling(request: TaskRequest): Promise<TaskResponse> {
    const input = this.extractGenericInput(request.prompt);
    const analysis = await this.performGenericDomainAnalysis(input);
    
    return {
      summary: 'General Domain Modeling Analysis',
      analysis: analysis.report,
      recommendations: analysis.recommendations,
      nextActions: analysis.nextActions,
      warnings: analysis.warnings,
      shouldBlockProgress: false,
    };
  }

  private classifyTask(description: string, prompt: string): string {
    const combined = (description + ' ' + prompt).toLowerCase();
    
    if (combined.includes('analyze domain') || combined.includes('domain analysis')) {
      return 'analyze-domain';
    }
    
    if (combined.includes('identify entities') || combined.includes('entity identification')) {
      return 'identify-entities';
    }
    
    if (combined.includes('aggregate') || combined.includes('aggregate root')) {
      return 'model-aggregates';
    }
    
    if (combined.includes('bounded context') || combined.includes('context boundary')) {
      return 'define-bounded-contexts';
    }
    
    if (combined.includes('business rule') || combined.includes('extract rules')) {
      return 'extract-business-rules';
    }
    
    if (combined.includes('ubiquitous language') || combined.includes('domain language')) {
      return 'create-ubiquitous-language';
    }
    
    if (combined.includes('domain service') || combined.includes('service design')) {
      return 'design-domain-services';
    }
    
    if (combined.includes('validate model') || combined.includes('model validation')) {
      return 'validate-domain-model';
    }
    
    return 'generic-modeling';
  }

  // Input extraction methods (simplified)
  // TODO: Implement input extraction logic (addressing Copilot review comment 2280080079)
  private extractDomainInput(prompt: string): any { return {}; }
  // TODO: Implement input extraction logic
  private extractEntityInput(prompt: string): any { return {}; }
  // TODO: Implement input extraction logic
  private extractAggregateInput(prompt: string): any { return {}; }
  // TODO: Implement input extraction logic
  private extractContextInput(prompt: string): any { return {}; }
  // TODO: Implement input extraction logic
  private extractBusinessRuleInput(prompt: string): any { return {}; }
  // TODO: Implement input extraction logic
  private extractLanguageInput(prompt: string): any { return {}; }
  // TODO: Implement input extraction logic
  private extractServiceInput(prompt: string): any { return {}; }
  // TODO: Implement input extraction logic
  private extractModelInput(prompt: string): any { return {}; }
  // TODO: Implement input extraction logic
  private extractGenericInput(prompt: string): any { return {}; }

  // Mock analysis methods (to be implemented with actual domain modeling logic)
  private async analyzeDomain(input: any): Promise<any> {
    return {
      entities: [
        { name: 'User', type: 'entity', description: 'System user' },
        { name: 'Order', type: 'aggregate', description: 'Customer order' },
      ],
      boundedContexts: [
        { name: 'User Management', description: 'Handles user operations', entities: ['User'] },
      ],
      businessRules: [
        { name: 'User Validation', description: 'Users must have valid email' },
      ],
      domainServices: [
        { name: 'UserService', description: 'User domain operations' },
      ],
      coreEntities: [
        { name: 'User', type: 'entity', description: 'Core user entity' },
      ],
      keyBusinessRules: [
        { name: 'Email Validation', description: 'Email must be unique' },
      ],
      complexityAnalysis: { high: ['Order'], medium: ['User'], simple: [] },
      complexityWarnings: [],
      criticalGaps: [],
    };
  }

  private async identifyEntities(input: any): Promise<any> {
    return {
      entities: [
        { name: 'User', type: 'entity', description: 'System user' },
      ],
      aggregateRoots: ['Order'],
      valueObjects: ['Email', 'Address'],
      domainServices: ['UserService'],
      relationships: [
        { from: 'User', type: 'has', to: 'Profile', cardinality: '1:1' },
      ],
      businessRuleCoverage: [
        { entity: 'User', rulesCount: 3 },
      ],
      warnings: [],
    };
  }

  private async modelAggregates(input: any): Promise<any> {
    return {
      aggregates: [
        {
          name: 'Order',
          description: 'Customer order aggregate',
          entities: ['OrderItem'],
          valueObjects: ['Money', 'Quantity'],
          businessRules: ['Order total calculation'],
          invariants: ['Order must have at least one item'],
        },
      ],
      boundaryAnalysis: [
        { aggregate: 'Order', boundaryStrength: 'strong', cohesion: 85 },
      ],
      dependencies: [],
      boundaryWarnings: [],
      criticalIssues: [],
    };
  }

  private async defineBoundedContexts(input: any): Promise<any> {
    return {
      contexts: [
        {
          name: 'Sales',
          description: 'Sales and order management',
          entities: ['Order', 'Customer'],
          services: ['OrderService'],
          responsibilities: ['Order processing', 'Customer management'],
        },
      ],
      relationships: [
        { upstream: 'Sales', downstream: 'Inventory', type: 'customer-supplier' },
      ],
      integrationPatterns: [
        {
          contexts: ['Sales', 'Inventory'],
          pattern: 'Event Sourcing',
          description: 'Order events trigger inventory updates',
        },
      ],
      integrationRisks: [],
    };
  }

  private async extractBusinessRules(input: any): Promise<any> {
    return {
      rules: [
        {
          name: 'Order Validation',
          description: 'Orders must have valid customer and items',
          type: 'constraint',
          priority: 'high',
        },
      ],
      complexityAnalysis: [
        { rule: 'Order Validation', complexity: 'medium', dependencies: 2 },
      ],
      entityMapping: [
        { entity: 'Order', rules: ['Order Validation'] },
      ],
      conflictingRules: [],
    };
  }

  private async createUbiquitousLanguage(input: any): Promise<any> {
    return {
      terms: [
        {
          term: 'Order',
          definition: 'Customer request for products',
          context: 'Sales',
        },
      ],
      coreTerms: [
        { term: 'Order', definition: 'Customer request', context: 'Sales' },
      ],
      supportingTerms: [],
      termRelationships: [
        { term1: 'Order', relationship: 'contains', term2: 'OrderItem' },
      ],
      ambiguousTerms: [],
    };
  }

  private async designDomainServices(input: any): Promise<any> {
    return {
      services: [
        {
          name: 'OrderService',
          description: 'Order processing service',
          operations: [
            {
              name: 'processOrder',
              description: 'Process customer order',
              inputs: [{ name: 'order', type: 'Order', required: true }],
              outputs: [{ name: 'result', type: 'OrderResult', required: true }],
              businessRule: 'Validate order before processing',
            },
          ],
          dependencies: ['PaymentService', 'InventoryService'],
        },
      ],
      dependencyAnalysis: [
        { service: 'OrderService', dependencies: 2, coupling: 'medium' },
      ],
      cohesionAnalysis: [
        { service: 'OrderService', cohesion: 85, responsibilities: 3 },
      ],
      designIssues: [],
    };
  }

  private async validateDomainModel(input: any): Promise<any> {
    return {
      score: 85,
      entityValidation: 90,
      relationshipValidation: 80,
      businessRuleValidation: 85,
      issues: [
        { severity: 'medium', description: 'Some relationships lack cardinality', category: 'relationships' },
      ],
      completeness: {
        entities: 90,
        relationships: 80,
        businessRules: 85,
        boundedContexts: 75,
      },
      consistencyChecks: [
        { category: 'Entity Names', status: 'passed', issues: 0 },
      ],
      recommendations: ['Add missing relationship cardinalities'],
      criticalIssues: [],
    };
  }

  private async performGenericDomainAnalysis(input: any): Promise<any> {
    return {
      report: 'General domain modeling analysis completed',
      recommendations: ['Continue with domain-driven design practices'],
      nextActions: ['Proceed to implementation phase'],
      warnings: [],
    };
  }

  private async analyzeRecentActivity(context: {
    recentFiles: string[];
    recentActions: string[];
    userIntent: string;
  }): Promise<{
    hasIncompleteModeling: boolean;
    hasModelingInconsistencies: boolean;
    shouldRefineModel: boolean;
    completionActions: string[];
    consistencyActions: string[];
    refinementActions: string[];
  }> {
    const hasModelFiles = context.recentFiles.some((f: string) => 
      f.includes('model') || f.includes('entity') || f.includes('domain')
    );
    
    const hasRequirementChanges = context.recentFiles.some((f: string) => 
      f.includes('requirement') || f.includes('story')
    );
    
    return {
      hasIncompleteModeling: !hasModelFiles && context.userIntent.includes('implement'),
      hasModelingInconsistencies: hasModelFiles && context.userIntent.includes('inconsistent'),
      shouldRefineModel: hasRequirementChanges && hasModelFiles,
      completionActions: [
        'Create comprehensive entity models',
        'Define aggregate boundaries',
        'Establish bounded contexts',
      ],
      consistencyActions: [
        'Review entity relationships',
        'Validate business rule consistency',
        'Check ubiquitous language usage',
      ],
      refinementActions: [
        'Update domain model based on new requirements',
        'Refine entity definitions',
        'Adjust aggregate boundaries if needed',
      ],
    };
  }
}

// Export for Claude Code Task tool integration
export const createDomainModelingTaskHandler = () => {
  const adapter = new DomainModelingTaskAdapter();
  
  return {
    handleTask: async (request: TaskRequest): Promise<TaskResponse> => {
      return adapter.handleDomainModelingTask(request);
    },
    
    provideProactiveGuidance: async (context: any): Promise<any> => {
      return adapter.provideProactiveGuidance(context);
    },
  };
};
