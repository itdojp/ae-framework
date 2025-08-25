import { z } from "zod";
export declare const FormalAgentConfig: z.ZodObject<{
    outputFormat: z.ZodDefault<z.ZodEnum<["tla+", "alloy", "z-notation", "openapi", "asyncapi", "graphql"]>>;
    validationLevel: z.ZodDefault<z.ZodEnum<["basic", "comprehensive", "formal-verification"]>>;
    generateDiagrams: z.ZodDefault<z.ZodBoolean>;
    enableModelChecking: z.ZodDefault<z.ZodBoolean>;
}, "strip", z.ZodTypeAny, {
    outputFormat?: "tla+" | "alloy" | "z-notation" | "openapi" | "asyncapi" | "graphql";
    validationLevel?: "basic" | "comprehensive" | "formal-verification";
    generateDiagrams?: boolean;
    enableModelChecking?: boolean;
}, {
    outputFormat?: "tla+" | "alloy" | "z-notation" | "openapi" | "asyncapi" | "graphql";
    validationLevel?: "basic" | "comprehensive" | "formal-verification";
    generateDiagrams?: boolean;
    enableModelChecking?: boolean;
}>;
export type FormalAgentConfig = z.infer<typeof FormalAgentConfig>;
export interface FormalSpecification {
    id: string;
    type: "tla+" | "alloy" | "z-notation" | "state-machine" | "contracts" | "api-spec";
    title: string;
    content: string;
    metadata: {
        version: string;
        author: string;
        created: Date;
        lastModified: Date;
        dependencies: string[];
        properties: string[];
    };
    validation: {
        status: "valid" | "invalid" | "pending";
        errors: ValidationError[];
        warnings: ValidationWarning[];
    };
}
export interface ValidationError {
    type: string;
    message: string;
    location?: {
        line: number;
        column: number;
    };
    severity: "error" | "warning" | "info";
}
export interface ValidationWarning {
    type: string;
    message: string;
    suggestion?: string;
}
export interface APISpecification {
    format: "openapi" | "asyncapi" | "graphql";
    version: string;
    content: string;
    endpoints: Endpoint[];
    schemas: SchemaDefinition[];
}
export interface Endpoint {
    path: string;
    method: string;
    description: string;
    parameters: Parameter[];
    responses: Response[];
    contracts: Contract[];
}
export interface Parameter {
    name: string;
    type: string;
    required: boolean;
    description?: string;
    constraints?: Constraint[];
}
export interface Response {
    status: number;
    description: string;
    schema?: string;
}
export interface SchemaDefinition {
    name: string;
    type: "object" | "array" | "primitive";
    properties: Record<string, any>;
    constraints: Constraint[];
}
export interface Constraint {
    type: "range" | "pattern" | "enum" | "custom";
    value: any;
    description?: string;
}
export interface Contract {
    type: "precondition" | "postcondition" | "invariant";
    expression: string;
    description: string;
}
export interface StateMachine {
    name: string;
    states: State[];
    transitions: Transition[];
    initialState: string;
    finalStates: string[];
    invariants: string[];
}
export interface State {
    name: string;
    type: "initial" | "intermediate" | "final" | "error";
    properties: Record<string, any>;
    invariants: string[];
}
export interface Transition {
    from: string;
    to: string;
    event: string;
    guard?: string;
    action?: string;
}
export interface ModelCheckingResult {
    specification: string;
    properties: PropertyResult[];
    counterExamples: CounterExample[];
    statistics: {
        statesExplored: number;
        timeElapsed: number;
        memoryUsed: number;
    };
}
export interface PropertyResult {
    name: string;
    satisfied: boolean;
    description: string;
    counterExample?: CounterExample;
}
export interface CounterExample {
    trace: TraceStep[];
    description: string;
}
export interface TraceStep {
    state: Record<string, any>;
    action: string;
    timestamp: number;
}
/**
 * Formal Agent - Phase 2 of ae-framework
 * Bridges Intent (Phase 1) and Tests (Phase 3) by generating formal, verifiable specifications
 */
export declare class FormalAgent {
    private config;
    private specifications;
    constructor(config?: Partial<FormalAgentConfig>);
    /**
     * Generate formal specifications from requirements
     */
    generateFormalSpecification(requirements: string, type?: "tla+" | "alloy" | "z-notation", options?: {
        includeDiagrams?: boolean;
        generateProperties?: boolean;
    }): Promise<FormalSpecification>;
    /**
     * Create API specifications (OpenAPI, AsyncAPI, GraphQL)
     */
    createAPISpecification(requirements: string, format?: "openapi" | "asyncapi" | "graphql", options?: {
        includeExamples?: boolean;
        generateContracts?: boolean;
    }): Promise<APISpecification>;
    /**
     * Generate state machines from requirements
     */
    generateStateMachine(requirements: string, options?: {
        generateInvariants?: boolean;
        includeDiagrams?: boolean;
    }): Promise<StateMachine>;
    /**
     * Create Design by Contract specifications
     */
    createContracts(functionSignature: string, requirements: string, options?: {
        includeInvariants?: boolean;
    }): Promise<Contract[]>;
    /**
     * Validate specification consistency and correctness
     */
    validateSpecification(specification: FormalSpecification): Promise<{
        status: "valid" | "invalid" | "pending";
        errors: ValidationError[];
        warnings: ValidationWarning[];
    }>;
    /**
     * Run formal model checking on specifications
     */
    runModelChecking(specification: FormalSpecification, properties?: string[], options?: {
        timeout?: number;
        maxStates?: number;
    }): Promise<ModelCheckingResult>;
    /**
     * Generate UML and sequence diagrams
     */
    generateDiagrams(specification: FormalSpecification, types?: ("sequence" | "state" | "class" | "component")[]): Promise<{
        type: string;
        content: string;
    }[]>;
    private generateId;
    private generateTLASpec;
    private generateAlloySpec;
    private generateZSpec;
    private generateOpenAPISpec;
    private generateAsyncAPISpec;
    private generateGraphQLSchema;
    private extractTitle;
    private extractModuleName;
    private extractVariables;
    private extractConstants;
    private extractActions;
    private extractEndpoints;
    private generateSchemas;
    private extractStates;
    private extractTransitions;
    private extractPreconditions;
    private extractPostconditions;
    private extractInvariants;
    private validateTLASpec;
    private validateAlloySpec;
    private validateZSpec;
    private validateStateMachine;
    private validateContracts;
    private validateAPISpec;
    private checkProperty;
    private estimateStatesExplored;
    private generateSequenceDiagram;
    private generateStateDiagram;
    private generateClassDiagram;
    private generateComponentDiagram;
    private generateSafetyProperty;
    private extractTLAProperties;
    private extractAlloyProperties;
    private extractZProperties;
    private extractAlloySignatures;
    private extractAlloyFacts;
    private extractAlloyPredicates;
    private extractZSchemas;
    private extractZOperations;
    private extractStateMachineName;
    private generateInvariants;
    private getParameterLocation;
    private mapToGraphQLType;
    getSpecifications(): FormalSpecification[];
    getSpecification(id: string): FormalSpecification | undefined;
    getConfig(): FormalAgentConfig;
    updateConfig(newConfig: Partial<FormalAgentConfig>): void;
}
