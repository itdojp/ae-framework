#!/usr/bin/env node

import { Server } from "@modelcontextprotocol/sdk/server/index.js";
import { StdioServerTransport } from "@modelcontextprotocol/sdk/server/stdio.js";
import {
  CallToolRequestSchema,
  ListToolsRequestSchema,
  ErrorCode,
  McpError,
} from "@modelcontextprotocol/sdk/types.js";
import { z } from "zod";
import { FormalAgent, FormalAgentConfig } from "../agents/formal-agent.js";

// Input schemas for MCP tools
const GenerateFormalSpecSchema = z.object({
  requirements: z.string().describe("The requirements to convert into formal specifications"),
  type: z.enum(["tla+", "alloy", "z-notation"]).default("tla+").describe("Type of formal specification to generate"),
  options: z.object({
    includeDiagrams: z.boolean().optional().describe("Whether to include diagrams"),
    generateProperties: z.boolean().optional().describe("Whether to generate properties for model checking"),
  }).optional(),
});

const CreateAPISpecSchema = z.object({
  requirements: z.string().describe("The requirements to convert into API specifications"),
  format: z.enum(["openapi", "asyncapi", "graphql"]).default("openapi").describe("API specification format"),
  options: z.object({
    includeExamples: z.boolean().optional().describe("Whether to include examples"),
    generateContracts: z.boolean().optional().describe("Whether to generate contracts"),
  }).optional(),
});

const GenerateStateMachineSchema = z.object({
  requirements: z.string().describe("The requirements to convert into state machine"),
  options: z.object({
    generateInvariants: z.boolean().optional().describe("Whether to generate invariants"),
    includeDiagrams: z.boolean().optional().describe("Whether to include state diagrams"),
  }).optional(),
});

const CreateContractsSchema = z.object({
  functionSignature: z.string().describe("The function signature to create contracts for"),
  requirements: z.string().describe("The requirements and behavior description"),
  options: z.object({
    includeInvariants: z.boolean().optional().describe("Whether to include class invariants"),
  }).optional(),
});

const ValidateSpecSchema = z.object({
  specificationId: z.string().describe("The ID of the specification to validate"),
  validationLevel: z.enum(["basic", "comprehensive", "formal-verification"]).optional().describe("Level of validation to perform"),
});

const ModelCheckSchema = z.object({
  specificationId: z.string().describe("The ID of the specification to model check"),
  properties: z.array(z.string()).optional().describe("Specific properties to check"),
  options: z.object({
    timeout: z.number().optional().describe("Timeout in milliseconds"),
    maxStates: z.number().optional().describe("Maximum number of states to explore"),
  }).optional(),
});

const GenerateDiagramsSchema = z.object({
  specificationId: z.string().describe("The ID of the specification to generate diagrams for"),
  types: z.array(z.enum(["sequence", "state", "class", "component"])).optional().describe("Types of diagrams to generate"),
});

const ListSpecificationsSchema = z.object({
  type: z.enum(["tla+", "alloy", "z-notation", "state-machine", "contracts", "api-spec"]).optional().describe("Filter by specification type"),
});

const GetSpecificationSchema = z.object({
  specificationId: z.string().describe("The ID of the specification to retrieve"),
});

const UpdateConfigSchema = z.object({
  config: z.object({
    outputFormat: z.enum(["tla+", "alloy", "z-notation", "openapi", "asyncapi", "graphql"]).optional(),
    validationLevel: z.enum(["basic", "comprehensive", "formal-verification"]).optional(),
    generateDiagrams: z.boolean().optional(),
    enableModelChecking: z.boolean().optional(),
  }).describe("Configuration updates for the Formal Agent"),
});

/**
 * MCP Server for Formal Agent
 * Provides tools for formal specification generation, validation, and model checking
 */
class FormalMCPServer {
  private server: Server;
  private formalAgent: FormalAgent;

  constructor() {
    this.server = new Server(
      {
        name: "formal-agent-server",
        version: "1.0.0",
      },
      {
        capabilities: {
          tools: {},
        },
      }
    );

    this.formalAgent = new FormalAgent();
    this.setupToolHandlers();
    this.setupErrorHandling();
  }

  private setupToolHandlers(): void {
    this.server.setRequestHandler(ListToolsRequestSchema, async () => {
      return {
        tools: [
          {
            name: "generate_formal_spec",
            description: "Generate formal specifications (TLA+, Alloy, Z notation) from requirements",
            inputSchema: GenerateFormalSpecSchema,
          },
          {
            name: "create_api_spec",
            description: "Create API specifications (OpenAPI, AsyncAPI, GraphQL schemas) from requirements",
            inputSchema: CreateAPISpecSchema,
          },
          {
            name: "generate_state_machine",
            description: "Generate state machine definitions from requirements",
            inputSchema: GenerateStateMachineSchema,
          },
          {
            name: "create_contracts",
            description: "Generate Design by Contract specifications for functions",
            inputSchema: CreateContractsSchema,
          },
          {
            name: "validate_spec",
            description: "Validate specification consistency and correctness",
            inputSchema: ValidateSpecSchema,
          },
          {
            name: "model_check",
            description: "Run formal model checking on specifications",
            inputSchema: ModelCheckSchema,
          },
          {
            name: "generate_diagrams",
            description: "Generate UML/sequence diagrams from specifications",
            inputSchema: GenerateDiagramsSchema,
          },
          {
            name: "list_specifications",
            description: "List all generated specifications with optional filtering",
            inputSchema: ListSpecificationsSchema,
          },
          {
            name: "get_specification",
            description: "Retrieve a specific specification by ID",
            inputSchema: GetSpecificationSchema,
          },
          {
            name: "update_config",
            description: "Update Formal Agent configuration",
            inputSchema: UpdateConfigSchema,
          },
        ],
      };
    });

    this.server.setRequestHandler(CallToolRequestSchema, async (request) => {
      const { name, arguments: args } = request.params;

      try {
        switch (name) {
          case "generate_formal_spec":
            return await this.handleGenerateFormalSpec(args);
          case "create_api_spec":
            return await this.handleCreateAPISpec(args);
          case "generate_state_machine":
            return await this.handleGenerateStateMachine(args);
          case "create_contracts":
            return await this.handleCreateContracts(args);
          case "validate_spec":
            return await this.handleValidateSpec(args);
          case "model_check":
            return await this.handleModelCheck(args);
          case "generate_diagrams":
            return await this.handleGenerateDiagrams(args);
          case "list_specifications":
            return await this.handleListSpecifications(args);
          case "get_specification":
            return await this.handleGetSpecification(args);
          case "update_config":
            return await this.handleUpdateConfig(args);
          default:
            throw new McpError(
              ErrorCode.MethodNotFound,
              `Unknown tool: ${name}`
            );
        }
      } catch (error) {
        if (error instanceof McpError) {
          throw error;
        }
        throw new McpError(
          ErrorCode.InternalError,
          `Error executing tool ${name}: ${error instanceof Error ? error.message : "Unknown error"}`
        );
      }
    });
  }

  private async handleGenerateFormalSpec(args: unknown) {
    const parsed = GenerateFormalSpecSchema.parse(args);
    const fo = parsed.options;
    const genSpecOpts = fo ? {
      ...(fo.includeDiagrams !== undefined ? { includeDiagrams: fo.includeDiagrams } : {}),
      ...(fo.generateProperties !== undefined ? { generateProperties: fo.generateProperties } : {}),
    } : {};
    const specification = await this.formalAgent.generateFormalSpecification(
      parsed.requirements,
      parsed.type,
      genSpecOpts
    );

    return {
      content: [
        {
          type: "text",
          text: JSON.stringify({
            success: true,
            specification: {
              id: specification.id,
              type: specification.type,
              title: specification.title,
              content: specification.content,
              metadata: specification.metadata,
              validation: specification.validation,
            },
          }, null, 2),
        },
      ],
    };
  }

  private async handleCreateAPISpec(args: unknown) {
    const parsed = CreateAPISpecSchema.parse(args);
    const ao = parsed.options;
    const apiOptions = ao ? {
      ...(ao.includeExamples !== undefined ? { includeExamples: ao.includeExamples } : {}),
      ...(ao.generateContracts !== undefined ? { generateContracts: ao.generateContracts } : {}),
    } : {};
    const apiSpec = await this.formalAgent.createAPISpecification(
      parsed.requirements,
      parsed.format,
      apiOptions
    );

    return {
      content: [
        {
          type: "text",
          text: JSON.stringify({
            success: true,
            apiSpecification: apiSpec,
          }, null, 2),
        },
      ],
    };
  }

  private async handleGenerateStateMachine(args: unknown) {
    const parsed = GenerateStateMachineSchema.parse(args);
    const so = parsed.options;
    const smOptions = so ? {
      ...(so.generateInvariants !== undefined ? { generateInvariants: so.generateInvariants } : {}),
      ...(so.includeDiagrams !== undefined ? { includeDiagrams: so.includeDiagrams } : {}),
    } : {};
    const stateMachine = await this.formalAgent.generateStateMachine(
      parsed.requirements,
      smOptions
    );

    return {
      content: [
        {
          type: "text",
          text: JSON.stringify({
            success: true,
            stateMachine: stateMachine,
          }, null, 2),
        },
      ],
    };
  }

  private async handleCreateContracts(args: unknown) {
    const parsed = CreateContractsSchema.parse(args);
    const co = parsed.options;
    const contractOptions = co ? {
      ...(co.includeInvariants !== undefined ? { includeInvariants: co.includeInvariants } : {}),
    } : {};
    const contracts = await this.formalAgent.createContracts(
      parsed.functionSignature,
      parsed.requirements,
      contractOptions
    );

    return {
      content: [
        {
          type: "text",
          text: JSON.stringify({
            success: true,
            contracts: contracts,
          }, null, 2),
        },
      ],
    };
  }

  private async handleValidateSpec(args: unknown) {
    const parsed = ValidateSpecSchema.parse(args);
    const specification = this.formalAgent.getSpecification(parsed.specificationId);
    
    if (!specification) {
      throw new McpError(
        ErrorCode.InvalidRequest,
        `Specification with ID ${parsed.specificationId} not found`
      );
    }

    // Update config if validation level is specified
    if (parsed.validationLevel) {
      this.formalAgent.updateConfig({ validationLevel: parsed.validationLevel });
    }

    const validation = await this.formalAgent.validateSpecification(specification);

    return {
      content: [
        {
          type: "text",
          text: JSON.stringify({
            success: true,
            specificationId: parsed.specificationId,
            validation: validation,
          }, null, 2),
        },
      ],
    };
  }

  private async handleModelCheck(args: unknown) {
    const parsed = ModelCheckSchema.parse(args);
    const specification = this.formalAgent.getSpecification(parsed.specificationId);
    
    if (!specification) {
      throw new McpError(
        ErrorCode.InvalidRequest,
        `Specification with ID ${parsed.specificationId} not found`
      );
    }

    const mo = parsed.options;
    const mcOptions = mo ? {
      ...(mo.timeout !== undefined ? { timeout: mo.timeout } : {}),
      ...(mo.maxStates !== undefined ? { maxStates: mo.maxStates } : {}),
    } : {};
    const modelCheckResult = await this.formalAgent.runModelChecking(
      specification,
      parsed.properties,
      mcOptions
    );

    return {
      content: [
        {
          type: "text",
          text: JSON.stringify({
            success: true,
            modelCheckingResult: modelCheckResult,
          }, null, 2),
        },
      ],
    };
  }

  private async handleGenerateDiagrams(args: unknown) {
    const parsed = GenerateDiagramsSchema.parse(args);
    const specification = this.formalAgent.getSpecification(parsed.specificationId);
    
    if (!specification) {
      throw new McpError(
        ErrorCode.InvalidRequest,
        `Specification with ID ${parsed.specificationId} not found`
      );
    }

    const diagrams = await this.formalAgent.generateDiagrams(
      specification,
      parsed.types || ["sequence", "state"]
    );

    return {
      content: [
        {
          type: "text",
          text: JSON.stringify({
            success: true,
            specificationId: parsed.specificationId,
            diagrams: diagrams,
          }, null, 2),
        },
      ],
    };
  }

  private async handleListSpecifications(args: unknown) {
    const parsed = ListSpecificationsSchema.parse(args);
    const allSpecs = this.formalAgent.getSpecifications();
    
    const filteredSpecs = parsed.type 
      ? allSpecs.filter(spec => spec.type === parsed.type)
      : allSpecs;

    return {
      content: [
        {
          type: "text",
          text: JSON.stringify({
            success: true,
            specifications: filteredSpecs.map(spec => ({
              id: spec.id,
              type: spec.type,
              title: spec.title,
              created: spec.metadata.created,
              lastModified: spec.metadata.lastModified,
              validationStatus: spec.validation.status,
            })),
            total: filteredSpecs.length,
          }, null, 2),
        },
      ],
    };
  }

  private async handleGetSpecification(args: unknown) {
    const parsed = GetSpecificationSchema.parse(args);
    const specification = this.formalAgent.getSpecification(parsed.specificationId);
    
    if (!specification) {
      throw new McpError(
        ErrorCode.InvalidRequest,
        `Specification with ID ${parsed.specificationId} not found`
      );
    }

    return {
      content: [
        {
          type: "text",
          text: JSON.stringify({
            success: true,
            specification: specification,
          }, null, 2),
        },
      ],
    };
  }

  private async handleUpdateConfig(args: unknown) {
    const parsed = UpdateConfigSchema.parse(args);
    
    const c = parsed.config;
    const cfg = {
      ...(c.outputFormat !== undefined ? { outputFormat: c.outputFormat } : {}),
      ...(c.validationLevel !== undefined ? { validationLevel: c.validationLevel } : {}),
      ...(c.generateDiagrams !== undefined ? { generateDiagrams: c.generateDiagrams } : {}),
      ...(c.enableModelChecking !== undefined ? { enableModelChecking: c.enableModelChecking } : {}),
    };
    this.formalAgent.updateConfig(cfg);
    const newConfig = this.formalAgent.getConfig();

    return {
      content: [
        {
          type: "text",
          text: JSON.stringify({
            success: true,
            message: "Configuration updated successfully",
            config: newConfig,
          }, null, 2),
        },
      ],
    };
  }

  private setupErrorHandling(): void {
    this.server.onerror = (error) => {
      console.error("[MCP Error]", error);
    };

    process.on('SIGINT', async () => {
      await this.server.close();
      process.exit(0);
    });
  }

  async run(): Promise<void> {
    const transport = new StdioServerTransport();
    await this.server.connect(transport);
    console.error("Formal Agent MCP Server running on stdio");
  }
}

// Helper function to create and run the server
export async function createFormalServer(): Promise<FormalMCPServer> {
  return new FormalMCPServer();
}

// CLI entry point
if (typeof require !== 'undefined' && require.main === module) {
  const server = new FormalMCPServer();
  server.run().catch(console.error);
}

export { FormalMCPServer };
