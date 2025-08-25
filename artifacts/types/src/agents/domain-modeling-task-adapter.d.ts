/**
 * Domain Modeling Task Adapter for Claude Code
 *
 * This adapter integrates Phase 5 (Domain Modeling) processing with Claude Code's
 * Task tool, enabling seamless domain analysis, entity modeling, and
 * architectural design workflows.
 */
import { TaskRequest, TaskResponse } from './task-types.js';
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
export declare class DomainModelingTaskAdapter {
    private agent;
    constructor();
    /**
     * Main handler for Domain Modeling tasks from Claude Code
     */
    handleDomainModelingTask(request: TaskRequest): Promise<TaskResponse>;
    /**
     * Proactive domain modeling guidance for Claude Code
     */
    provideProactiveGuidance(context: {
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
    }>;
    private handleDomainAnalysis;
    private handleEntityIdentification;
    private handleAggregateModeling;
    private handleBoundedContextDefinition;
    private handleBusinessRuleExtraction;
    private handleUbiquitousLanguageCreation;
    private handleDomainServiceDesign;
    private handleDomainModelValidation;
    private handleGenericDomainModeling;
    private classifyTask;
    private extractDomainInput;
    private extractEntityInput;
    private extractAggregateInput;
    private extractContextInput;
    private extractBusinessRuleInput;
    private extractLanguageInput;
    private extractServiceInput;
    private extractModelInput;
    private extractGenericInput;
    private analyzeDomain;
    private identifyEntities;
    private modelAggregates;
    private defineBoundedContexts;
    private extractBusinessRules;
    private createUbiquitousLanguage;
    private designDomainServices;
    private validateDomainModel;
    private performGenericDomainAnalysis;
    private analyzeRecentActivity;
}
export declare const createDomainModelingTaskHandler: () => {
    handleTask: (request: TaskRequest) => Promise<TaskResponse>;
    provideProactiveGuidance: (context: any) => Promise<any>;
};
