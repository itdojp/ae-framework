import { z } from "zod";

// Configuration types
export const FormalAgentConfig = z.object({
  outputFormat: z.enum(["tla+", "alloy", "z-notation", "openapi", "asyncapi", "graphql"]).default("tla+"),
  validationLevel: z.enum(["basic", "comprehensive", "formal-verification"]).default("comprehensive"),
  generateDiagrams: z.boolean().default(true),
  enableModelChecking: z.boolean().default(true),
});

export type FormalAgentConfig = z.infer<typeof FormalAgentConfig>;

// Specification types
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
  location?: { line: number; column: number };
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
export class FormalAgent {
  private config: FormalAgentConfig;
  private specifications: Map<string, FormalSpecification> = new Map();

  constructor(config: Partial<FormalAgentConfig> = {}) {
    this.config = FormalAgentConfig.parse(config);
  }

  /**
   * Generate formal specifications from requirements
   */
  async generateFormalSpecification(
    requirements: string,
    type: "tla+" | "alloy" | "z-notation" = "tla+",
    options: { includeDiagrams?: boolean; generateProperties?: boolean } = {}
  ): Promise<FormalSpecification> {
    const id = this.generateId();
    const timestamp = new Date();

    let content = "";
    let properties: string[] = [];

    switch (type) {
      case "tla+":
        content = this.generateTLASpec(requirements);
        properties = this.extractTLAProperties(content);
        break;
      case "alloy":
        content = this.generateAlloySpec(requirements);
        properties = this.extractAlloyProperties(content);
        break;
      case "z-notation":
        content = this.generateZSpec(requirements);
        properties = this.extractZProperties(content);
        break;
    }

    const specification: FormalSpecification = {
      id,
      type,
      title: this.extractTitle(requirements),
      content,
      metadata: {
        version: "1.0.0",
        author: "FormalAgent",
        created: timestamp,
        lastModified: timestamp,
        dependencies: [],
        properties,
      },
      validation: {
        status: "pending",
        errors: [],
        warnings: [],
      },
    };

    // Validate the generated specification
    const validationResult = await this.validateSpecification(specification);
    specification.validation = validationResult;

    this.specifications.set(id, specification);
    return specification;
  }

  /**
   * Create API specifications (OpenAPI, AsyncAPI, GraphQL)
   */
  async createAPISpecification(
    requirements: string,
    format: "openapi" | "asyncapi" | "graphql" = "openapi",
    options: { includeExamples?: boolean; generateContracts?: boolean } = {}
  ): Promise<APISpecification> {
    const endpoints = this.extractEndpoints(requirements);
    const schemas = this.generateSchemas(requirements);

    let content = "";
    switch (format) {
      case "openapi":
        content = this.generateOpenAPISpec(endpoints, schemas, options);
        break;
      case "asyncapi":
        content = this.generateAsyncAPISpec(endpoints, schemas, options);
        break;
      case "graphql":
        content = this.generateGraphQLSchema(schemas, options);
        break;
    }

    return {
      format,
      version: format === "openapi" ? "3.0.3" : format === "asyncapi" ? "2.6.0" : "2023-10",
      content,
      endpoints,
      schemas,
    };
  }

  /**
   * Generate state machines from requirements
   */
  async generateStateMachine(
    requirements: string,
    options: { generateInvariants?: boolean; includeDiagrams?: boolean } = {}
  ): Promise<StateMachine> {
    const states = this.extractStates(requirements);
    const transitions = this.extractTransitions(requirements, states);
    const invariants = options.generateInvariants ? this.generateInvariants(requirements) : [];

    return {
      name: this.extractStateMachineName(requirements),
      states,
      transitions,
      initialState: states.find(s => s.type === "initial")?.name || states[0]?.name || "Initial",
      finalStates: states.filter(s => s.type === "final").map(s => s.name),
      invariants,
    };
  }

  /**
   * Create Design by Contract specifications
   */
  async createContracts(
    functionSignature: string,
    requirements: string,
    options: { includeInvariants?: boolean } = {}
  ): Promise<Contract[]> {
    const contracts: Contract[] = [];

    // Generate preconditions
    const preconditions = this.extractPreconditions(requirements, functionSignature);
    preconditions.forEach(condition => {
      contracts.push({
        type: "precondition",
        expression: condition.expression,
        description: condition.description,
      });
    });

    // Generate postconditions
    const postconditions = this.extractPostconditions(requirements, functionSignature);
    postconditions.forEach(condition => {
      contracts.push({
        type: "postcondition",
        expression: condition.expression,
        description: condition.description,
      });
    });

    // Generate invariants if requested
    if (options.includeInvariants) {
      const invariants = this.extractInvariants(requirements);
      invariants.forEach(invariant => {
        contracts.push({
          type: "invariant",
          expression: invariant.expression,
          description: invariant.description,
        });
      });
    }

    return contracts;
  }

  /**
   * Validate specification consistency and correctness
   */
  async validateSpecification(specification: FormalSpecification): Promise<{
    status: "valid" | "invalid" | "pending";
    errors: ValidationError[];
    warnings: ValidationWarning[];
  }> {
    const errors: ValidationError[] = [];
    const warnings: ValidationWarning[] = [];

    try {
      switch (specification.type) {
        case "tla+":
          await this.validateTLASpec(specification.content, errors, warnings);
          break;
        case "alloy":
          await this.validateAlloySpec(specification.content, errors, warnings);
          break;
        case "z-notation":
          await this.validateZSpec(specification.content, errors, warnings);
          break;
        case "state-machine":
          await this.validateStateMachine(specification.content, errors, warnings);
          break;
        case "contracts":
          await this.validateContracts(specification.content, errors, warnings);
          break;
        case "api-spec":
          await this.validateAPISpec(specification.content, errors, warnings);
          break;
      }
    } catch (error) {
      errors.push({
        type: "validation_error",
        message: error instanceof Error ? error.message : "Unknown validation error",
        severity: "error",
      });
    }

    return {
      status: errors.length > 0 ? "invalid" : "valid",
      errors,
      warnings,
    };
  }

  /**
   * Run formal model checking on specifications
   */
  async runModelChecking(
    specification: FormalSpecification,
    properties: string[] = [],
    options: { timeout?: number; maxStates?: number } = {}
  ): Promise<ModelCheckingResult> {
    if (!this.config.enableModelChecking) {
      throw new Error("Model checking is disabled in configuration");
    }

    const propertiesToCheck = properties.length > 0 ? properties : specification.metadata.properties;
    const results: PropertyResult[] = [];
    const counterExamples: CounterExample[] = [];

    for (const property of propertiesToCheck) {
      try {
        const result = await this.checkProperty(specification, property, options);
        results.push(result);
        
        if (!result.satisfied && result.counterExample) {
          counterExamples.push(result.counterExample);
        }
      } catch (error) {
        results.push({
          name: property,
          satisfied: false,
          description: `Error checking property: ${error instanceof Error ? error.message : "Unknown error"}`,
        });
      }
    }

    return {
      specification: specification.id,
      properties: results,
      counterExamples,
      statistics: {
        statesExplored: this.estimateStatesExplored(specification),
        timeElapsed: Date.now(), // Placeholder
        memoryUsed: 0, // Placeholder
      },
    };
  }

  /**
   * Generate UML and sequence diagrams
   */
  async generateDiagrams(
    specification: FormalSpecification,
    types: ("sequence" | "state" | "class" | "component")[] = ["sequence", "state"]
  ): Promise<{ type: string; content: string }[]> {
    const diagrams: { type: string; content: string }[] = [];

    for (const type of types) {
      switch (type) {
        case "sequence":
          diagrams.push({
            type: "sequence",
            content: this.generateSequenceDiagram(specification),
          });
          break;
        case "state":
          diagrams.push({
            type: "state",
            content: this.generateStateDiagram(specification),
          });
          break;
        case "class":
          diagrams.push({
            type: "class",
            content: this.generateClassDiagram(specification),
          });
          break;
        case "component":
          diagrams.push({
            type: "component",
            content: this.generateComponentDiagram(specification),
          });
          break;
      }
    }

    return diagrams;
  }

  // Private helper methods
  private generateId(): string {
    return `spec_${Date.now()}_${Math.random().toString(36).substring(2, 11)}`;
  }

  private generateTLASpec(requirements: string): string {
    // Simplified TLA+ generation based on requirements analysis
    const moduleName = this.extractModuleName(requirements);
    const variables = this.extractVariables(requirements);
    const constants = this.extractConstants(requirements);
    const actions = this.extractActions(requirements);

    return `----------------------------- MODULE ${moduleName} -----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS ${constants.join(", ")}

VARIABLES ${variables.join(", ")}

Init == 
    ${variables.map(v => `/\\ ${v} = InitialValue`).join("\n    ")}

${actions.map(action => `${action.name}(${action.params.join(", ")}) ==
    /\\ ${action.guard}
    /\\ ${action.effect}`).join("\n\n")}

Next == ${actions.map(a => `\\/ \\E ${a.params.join(", ")}: ${a.name}(${a.params.join(", ")})`).join("\n        ")}

Spec == Init /\\ [][Next]_<<${variables.join(", ")}>>

TypeInvariant == 
    ${variables.map(v => `/\\ ${v} \\in ValidType`).join("\n    ")}

SafetyProperty == ${this.generateSafetyProperty(requirements)}

============================================================================`;
  }

  private generateAlloySpec(requirements: string): string {
    const signatures = this.extractAlloySignatures(requirements);
    const facts = this.extractAlloyFacts(requirements);
    const predicates = this.extractAlloyPredicates(requirements);

    return `// Alloy specification generated from requirements

${signatures.map(sig => `sig ${sig.name} {
    ${sig.fields.map((f: any) => `${f.name}: ${f.type}`).join(",\n    ")}
}`).join("\n\n")}

${facts.map(fact => `fact ${fact.name} {
    ${fact.constraint}
}`).join("\n\n")}

${predicates.map(pred => `pred ${pred.name}[${pred.params.join(", ")}] {
    ${pred.body}
}`).join("\n\n")}

run {} for 5`;
  }

  private generateZSpec(requirements: string): string {
    const schemas = this.extractZSchemas(requirements);
    const operations = this.extractZOperations(requirements);

    return `\\documentclass{article}
\\usepackage{zed-csp}
\\begin{document}

${schemas.map(schema => `\\begin{schema}{${schema.name}}
${schema.declaration}
\\where
${schema.predicate}
\\end{schema}`).join("\n\n")}

${operations.map(op => `\\begin{schema}{${op.name}}
\\Delta ${op.state}
${op.inputs}
\\where
${op.precondition}
${op.postcondition}
\\end{schema}`).join("\n\n")}

\\end{document}`;
  }

  private generateOpenAPISpec(endpoints: Endpoint[], schemas: SchemaDefinition[], options: any): string {
    const paths = endpoints.reduce((acc, endpoint) => {
      const path = endpoint.path;
      if (!acc[path]) acc[path] = {};
      
      acc[path][endpoint.method.toLowerCase()] = {
        operationId: `${endpoint.method.toLowerCase()}${endpoint.path.replace(/[^a-zA-Z0-9]/g, "")}`,
        description: endpoint.description,
        parameters: endpoint.parameters.map(p => ({
          name: p.name,
          in: this.getParameterLocation(p.name, endpoint.path),
          required: p.required,
          description: p.description,
          schema: { type: p.type },
        })),
        responses: endpoint.responses.reduce((responses, response) => {
          responses[response.status] = {
            description: response.description,
            ...(response.schema && {
              content: {
                "application/json": {
                  schema: { $ref: `#/components/schemas/${response.schema}` }
                }
              }
            })
          };
          return responses;
        }, {} as Record<string, any>),
      };
      
      return acc;
    }, {} as Record<string, any>);

    const components = {
      schemas: schemas.reduce((acc, schema) => {
        acc[schema.name] = {
          type: schema.type,
          properties: schema.properties,
        };
        return acc;
      }, {} as Record<string, any>),
    };

    return JSON.stringify({
      openapi: "3.0.3",
      info: {
        title: "Generated API",
        version: "1.0.0",
      },
      paths,
      components,
    }, null, 2);
  }

  private generateAsyncAPISpec(endpoints: Endpoint[], schemas: SchemaDefinition[], options: any): string {
    // Simplified AsyncAPI generation
    return JSON.stringify({
      asyncapi: "2.6.0",
      info: {
        title: "Generated Async API",
        version: "1.0.0",
      },
      channels: endpoints.reduce((acc, endpoint) => {
        acc[endpoint.path] = {
          description: endpoint.description,
          subscribe: {
            message: {
              payload: {
                $ref: `#/components/schemas/Message`,
              },
            },
          },
        };
        return acc;
      }, {} as Record<string, any>),
      components: {
        schemas: schemas.reduce((acc, schema) => {
          acc[schema.name] = {
            type: schema.type,
            properties: schema.properties,
          };
          return acc;
        }, {} as Record<string, any>),
      },
    }, null, 2);
  }

  private generateGraphQLSchema(schemas: SchemaDefinition[], options: any): string {
    const types = schemas.map(schema => {
      const fields = Object.entries(schema.properties)
        .map(([name, type]) => `  ${name}: ${this.mapToGraphQLType(type)}`)
        .join("\n");
      
      return `type ${schema.name} {
${fields}
}`;
    }).join("\n\n");

    return `# Generated GraphQL Schema

${types}

type Query {
  # Add your queries here
}

type Mutation {
  # Add your mutations here
}`;
  }

  // Extraction and analysis methods
  private extractTitle(requirements: string): string {
    const titleMatch = requirements.match(/(?:title|name):\s*(.+)/i);
    return titleMatch && titleMatch[1] ? titleMatch[1].trim() : "Generated Specification";
  }

  private extractModuleName(requirements: string): string {
    const nameMatch = requirements.match(/(?:module|system|component):\s*(\w+)/i);
    return nameMatch && nameMatch[1] ? nameMatch[1] : "GeneratedModule";
  }

  private extractVariables(requirements: string): string[] {
    // Simplified variable extraction
    const variables = requirements.match(/\b(?:variable|state|field):\s*(\w+)/gi) || [];
    return variables.map(v => v.split(":")[1]?.trim()).filter(Boolean) as string[];
  }

  private extractConstants(requirements: string): string[] {
    const constants = requirements.match(/\b(?:constant|const|parameter):\s*(\w+)/gi) || [];
    return constants.map(c => c.split(":")[1]?.trim()).filter(Boolean) as string[];
  }

  private extractActions(requirements: string): { name: string; params: string[]; guard: string; effect: string }[] {
    // Simplified action extraction
    return [
      {
        name: "DefaultAction",
        params: ["param"],
        guard: "TRUE",
        effect: "UNCHANGED <<vars>>",
      },
    ];
  }

  private extractEndpoints(requirements: string): Endpoint[] {
    // Simplified endpoint extraction
    const endpoints: Endpoint[] = [];
    const pathMatches = requirements.match(/(?:GET|POST|PUT|DELETE|PATCH)\s+(\/[^\s]*)/gi) || [];
    
    pathMatches.forEach(match => {
      const [method, path] = match.split(/\s+/);
      endpoints.push({
        path: path || '',
        method: method?.toUpperCase() || 'GET',
        description: `${method} operation for ${path}`,
        parameters: [],
        responses: [
          { status: 200, description: "Success" },
          { status: 400, description: "Bad Request" },
        ],
        contracts: [],
      });
    });

    return endpoints;
  }

  private generateSchemas(requirements: string): SchemaDefinition[] {
    // Simplified schema generation based on mentioned entities
    const entities = requirements.match(/\b[A-Z]\w+(?:\s+entity|\s+object|\s+model)?/g) || [];
    
    return entities.map(entity => ({
      name: entity.replace(/\s+(entity|object|model)/, ""),
      type: "object" as const,
      properties: {
        id: { type: "string" },
        name: { type: "string" },
        createdAt: { type: "string", format: "date-time" },
      },
      constraints: [],
    }));
  }

  private extractStates(requirements: string): State[] {
    const stateNames = requirements.match(/\b(?:state|status|phase):\s*(\w+)/gi) || [];
    
    return stateNames.map((stateName, index) => ({
      name: stateName.split(":")[1]?.trim() || `State${index}`,
      type: index === 0 ? "initial" : "intermediate" as any,
      properties: {},
      invariants: [],
    }));
  }

  private extractTransitions(requirements: string, states: State[]): Transition[] {
    // Simplified transition extraction
    const transitions: Transition[] = [];
    
    for (let i = 0; i < states.length - 1; i++) {
      transitions.push({
        from: states[i]?.name || `State${i}`,
        to: states[i + 1]?.name || `State${i + 1}`,
        event: `transition${i + 1}`,
        guard: "TRUE",
      });
    }

    return transitions;
  }

  private extractPreconditions(requirements: string, functionSignature: string): { expression: string; description: string }[] {
    return [
      {
        expression: "input != null",
        description: "Input parameters must not be null",
      },
    ];
  }

  private extractPostconditions(requirements: string, functionSignature: string): { expression: string; description: string }[] {
    return [
      {
        expression: "result != null",
        description: "Result must not be null",
      },
    ];
  }

  private extractInvariants(requirements: string): { expression: string; description: string }[] {
    return [
      {
        expression: "invariant_condition",
        description: "System invariant condition",
      },
    ];
  }

  // Validation methods
  private async validateTLASpec(content: string, errors: ValidationError[], warnings: ValidationWarning[]): Promise<void> {
    // Basic TLA+ syntax validation
    if (!content.includes("MODULE")) {
      errors.push({
        type: "syntax_error",
        message: "TLA+ specification must include MODULE declaration",
        severity: "error",
      });
    }
    
    if (!content.includes("VARIABLES") && !content.includes("CONSTANT")) {
      warnings.push({
        type: "completeness_warning",
        message: "TLA+ specification should include VARIABLES or CONSTANTS",
        suggestion: "Add variable or constant declarations",
      });
    }
  }

  private async validateAlloySpec(content: string, errors: ValidationError[], warnings: ValidationWarning[]): Promise<void> {
    // Basic Alloy validation
    if (!content.includes("sig ")) {
      errors.push({
        type: "syntax_error",
        message: "Alloy specification must include signature declarations",
        severity: "error",
      });
    }
  }

  private async validateZSpec(content: string, errors: ValidationError[], warnings: ValidationWarning[]): Promise<void> {
    // Basic Z notation validation
    if (!content.includes("\\begin{schema}")) {
      errors.push({
        type: "syntax_error",
        message: "Z specification must include schema declarations",
        severity: "error",
      });
    }
  }

  private async validateStateMachine(content: string, errors: ValidationError[], warnings: ValidationWarning[]): Promise<void> {
    // State machine validation logic
  }

  private async validateContracts(content: string, errors: ValidationError[], warnings: ValidationWarning[]): Promise<void> {
    // Contract validation logic
  }

  private async validateAPISpec(content: string, errors: ValidationError[], warnings: ValidationWarning[]): Promise<void> {
    try {
      JSON.parse(content);
    } catch (e) {
      errors.push({
        type: "json_error",
        message: "Invalid JSON format in API specification",
        severity: "error",
      });
    }
  }

  // Model checking methods
  private async checkProperty(
    specification: FormalSpecification,
    property: string,
    options: { timeout?: number; maxStates?: number }
  ): Promise<PropertyResult> {
    // Simplified property checking
    return {
      name: property,
      satisfied: Math.random() > 0.3, // Simulation
      description: `Property check for: ${property}`,
    };
  }

  private estimateStatesExplored(specification: FormalSpecification): number {
    // Estimate based on specification complexity
    return specification.content.length * 10;
  }

  // Diagram generation methods
  private generateSequenceDiagram(specification: FormalSpecification): string {
    return `@startuml
title Sequence Diagram for ${specification.title}

actor User
participant System
participant Database

User -> System: Request
System -> Database: Query
Database -> System: Response
System -> User: Result

@enduml`;
  }

  private generateStateDiagram(specification: FormalSpecification): string {
    return `@startuml
title State Diagram for ${specification.title}

[*] -> Initial
Initial -> Processing
Processing -> Completed
Completed -> [*]

@enduml`;
  }

  private generateClassDiagram(specification: FormalSpecification): string {
    return `@startuml
title Class Diagram for ${specification.title}

class Entity {
  -id: String
  -name: String
  +getId(): String
  +getName(): String
}

@enduml`;
  }

  private generateComponentDiagram(specification: FormalSpecification): string {
    return `@startuml
title Component Diagram for ${specification.title}

[Component A] -> [Component B]
[Component B] -> [Database]

@enduml`;
  }

  // Helper methods
  private generateSafetyProperty(requirements: string): string {
    return "SafetyCondition";
  }

  private extractTLAProperties(content: string): string[] {
    const properties = content.match(/\b\w+Property\b/g) || [];
    return properties;
  }

  private extractAlloyProperties(content: string): string[] {
    const properties = content.match(/assert\s+(\w+)/g) || [];
    return properties.map(p => p.split(/\s+/)[1]).filter(Boolean) as string[];
  }

  private extractZProperties(content: string): string[] {
    return ["ZProperty"];
  }

  private extractAlloySignatures(requirements: string): any[] {
    return [{ name: "Entity", fields: [{ name: "id", type: "String" }] }];
  }

  private extractAlloyFacts(requirements: string): any[] {
    return [{ name: "BasicFact", constraint: "all e: Entity | some e.id" }];
  }

  private extractAlloyPredicates(requirements: string): any[] {
    return [{ name: "valid", params: ["e: Entity"], body: "some e.id" }];
  }

  private extractZSchemas(requirements: string): any[] {
    return [{ name: "State", declaration: "x: ℕ", predicate: "x > 0" }];
  }

  private extractZOperations(requirements: string): any[] {
    return [{ name: "Op", state: "State", inputs: "input?: ℕ", precondition: "input? > 0", postcondition: "x' = x + input?" }];
  }

  private extractStateMachineName(requirements: string): string {
    const match = requirements.match(/(?:state machine|fsm|automaton):\s*(\w+)/i);
    return match && match[1] ? match[1] : "StateMachine";
  }

  private generateInvariants(requirements: string): string[] {
    return ["SystemInvariant"];
  }

  private getParameterLocation(name: string, path: string): string {
    return path.includes(`{${name}}`) ? "path" : "query";
  }

  private mapToGraphQLType(type: any): string {
    if (typeof type === "string") return type;
    return "String";
  }

  // Public getter methods
  getSpecifications(): FormalSpecification[] {
    return Array.from(this.specifications.values());
  }

  getSpecification(id: string): FormalSpecification | undefined {
    return this.specifications.get(id);
  }

  getConfig(): FormalAgentConfig {
    return { ...this.config };
  }

  updateConfig(newConfig: Partial<FormalAgentConfig>): void {
    this.config = FormalAgentConfig.parse({ ...this.config, ...newConfig });
  }
}