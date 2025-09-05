#!/usr/bin/env node

import { Server } from '@modelcontextprotocol/sdk/server/index.js';
import { StdioServerTransport } from '@modelcontextprotocol/sdk/server/stdio.js';
import {
  CallToolRequestSchema,
  ListToolsRequestSchema,
} from '@modelcontextprotocol/sdk/types.js';
import { TestGenerationAgent } from '../agents/test-generation-agent.js';
import {
  BDDArgsSchema,
  DesignPerformanceArgsSchema,
  GenerateFromCodeArgsSchema,
  GenerateFromRequirementsArgsSchema,
  PlanIntegrationArgsSchema,
  PropertyTestsArgsSchema,
  SecurityTestsArgsSchema,
  AnalyzeCoverageArgsSchema,
  parseOrThrow,
  type BDDArgs,
  type DesignPerformanceArgs,
  type GenerateFromCodeArgs,
  type GenerateFromRequirementsArgs,
  type PlanIntegrationArgs,
  type PropertyTestsArgs,
  type SecurityTestsArgs,
  type AnalyzeCoverageArgs,
} from './schemas.js';

/**
 * Test Generation MCP Server
 * Provides automated test generation and design capabilities
 */
class TestGenerationServer {
  private server: Server;
  private agent: TestGenerationAgent;

  constructor() {
    this.agent = new TestGenerationAgent();
    this.server = new Server(
      {
        name: 'test-generation',
        version: '1.0.0',
      },
      {
        capabilities: {
          tools: {},
        },
      }
    );

    this.setupToolHandlers();
  }

  private setupToolHandlers() {
    this.server.setRequestHandler(ListToolsRequestSchema, async () => ({
      tools: [
        {
          name: 'generate_tests_from_requirements',
          description: 'Generate comprehensive test cases from requirements',
          inputSchema: {
            type: 'object',
            properties: {
              feature: {
                type: 'string',
                description: 'Feature name or description',
              },
              requirements: {
                type: 'array',
                items: { type: 'string' },
                description: 'List of requirements',
              },
              testFramework: {
                type: 'string',
                enum: ['vitest', 'jest', 'mocha'],
                description: 'Test framework to use',
                default: 'vitest',
              },
            },
            required: ['feature'],
          },
        },
        {
          name: 'generate_tests_from_code',
          description: 'Generate tests by analyzing existing code (Reverse TDD)',
          inputSchema: {
            type: 'object',
            properties: {
              codeFile: {
                type: 'string',
                description: 'Path to the code file to analyze',
              },
            },
            required: ['codeFile'],
          },
        },
        {
          name: 'generate_property_tests',
          description: 'Design property-based tests from contracts',
          inputSchema: {
            type: 'object',
            properties: {
              functionName: {
                type: 'string',
                description: 'Function to test',
              },
              inputs: {
                type: 'array',
                items: {
                  type: 'object',
                  properties: {
                    name: { type: 'string' },
                    type: { type: 'string' },
                    constraints: {
                      type: 'array',
                      items: { type: 'string' },
                    },
                  },
                },
              },
              invariants: {
                type: 'array',
                items: { type: 'string' },
                description: 'Properties that should always hold',
              },
            },
            required: ['functionName', 'inputs', 'invariants'],
          },
        },
        {
          name: 'generate_bdd_scenarios',
          description: 'Generate BDD scenarios from user stories',
          inputSchema: {
            type: 'object',
            properties: {
              title: {
                type: 'string',
                description: 'User story title',
              },
              asA: {
                type: 'string',
                description: 'User role',
              },
              iWant: {
                type: 'string',
                description: 'Desired functionality',
              },
              soThat: {
                type: 'string',
                description: 'Business value',
              },
              acceptanceCriteria: {
                type: 'array',
                items: { type: 'string' },
                description: 'Acceptance criteria',
              },
            },
            required: ['title', 'asA', 'iWant', 'soThat'],
          },
        },
        {
          name: 'plan_integration_tests',
          description: 'Design integration test strategy for system architecture',
          inputSchema: {
            type: 'object',
            properties: {
              services: {
                type: 'array',
                items: {
                  type: 'object',
                  properties: {
                    name: { type: 'string' },
                    dependencies: {
                      type: 'array',
                      items: { type: 'string' },
                    },
                  },
                },
                description: 'Service architecture',
              },
              dataFlow: {
                type: 'array',
                items: {
                  type: 'object',
                  properties: {
                    from: { type: 'string' },
                    to: { type: 'string' },
                    data: { type: 'string' },
                  },
                },
                description: 'Data flow between services',
              },
            },
            required: ['services'],
          },
        },
        {
          name: 'generate_security_tests',
          description: 'Generate security tests based on OWASP guidelines',
          inputSchema: {
            type: 'object',
            properties: {
              endpoint: {
                type: 'object',
                properties: {
                  path: { type: 'string' },
                  method: { type: 'string' },
                  authentication: { type: 'boolean' },
                  authorization: {
                    type: 'array',
                    items: { type: 'string' },
                  },
                  inputs: {
                    type: 'array',
                    items: { type: 'object' },
                  },
                },
                required: ['path', 'method'],
              },
            },
            required: ['endpoint'],
          },
        },
        {
          name: 'design_performance_tests',
          description: 'Design performance test suite based on SLA requirements',
          inputSchema: {
            type: 'object',
            properties: {
              sla: {
                type: 'object',
                properties: {
                  responseTime: {
                    type: 'number',
                    description: 'Max response time in ms',
                  },
                  throughput: {
                    type: 'number',
                    description: 'Requests per second',
                  },
                  concurrentUsers: {
                    type: 'number',
                    description: 'Number of concurrent users',
                  },
                  availability: {
                    type: 'number',
                    description: 'Required availability percentage',
                  },
                },
              },
            },
            required: ['sla'],
          },
        },
        {
          name: 'analyze_test_coverage',
          description: 'Analyze and recommend improvements for test coverage',
          inputSchema: {
            type: 'object',
            properties: {
              projectPath: {
                type: 'string',
                description: 'Path to project root',
                default: '.',
              },
            },
          },
        },
      ],
    }));

    this.server.setRequestHandler(CallToolRequestSchema, async (request) => {
      const { name, arguments: args } = request.params;

      try {
        switch (name) {
          case 'generate_tests_from_requirements':
            return await this.handleGenerateTestsFromRequirements(args);

          case 'generate_tests_from_code':
            return await this.handleGenerateTestsFromCode(args);

          case 'generate_property_tests':
            return await this.handleGeneratePropertyTests(args);

          case 'generate_bdd_scenarios':
            return await this.handleGenerateBDDScenarios(args);

          case 'plan_integration_tests':
            return await this.handlePlanIntegrationTests(args);

          case 'generate_security_tests':
            return await this.handleGenerateSecurityTests(args);

          case 'design_performance_tests':
            return await this.handleDesignPerformanceTests(args);

          case 'analyze_test_coverage':
            return await this.handleAnalyzeTestCoverage(args);

          default:
            throw new Error(`Unknown tool: ${name}`);
        }
      } catch (error: unknown) {
        return {
          content: [
            {
              type: 'text',
              text: `Error: ${(error as Error).message}`,
            },
          ],
        };
      }
    });
  }

  private async handleGenerateTestsFromRequirements(args: unknown) {
    const parsed: GenerateFromRequirementsArgs = parseOrThrow(GenerateFromRequirementsArgsSchema, args);
    const result = await this.agent.generateTestsFromRequirements({
      feature: parsed.feature,
      requirements: parsed.requirements,
      testFramework: parsed.testFramework,
    });

    const response = this.formatTestGenerationResult(result);
    
    return {
      content: [{ type: 'text', text: response }],
    };
  }

  private async handleGenerateTestsFromCode(args: unknown) {
    const parsed: GenerateFromCodeArgs = parseOrThrow(GenerateFromCodeArgsSchema, args);
    const result = await this.agent.generateTestsFromCode(parsed.codeFile);
    const response = this.formatTestGenerationResult(result);
    
    return {
      content: [{ type: 'text', text: response }],
    };
  }

  private async handleGeneratePropertyTests(args: unknown) {
    const parsed: PropertyTestsArgs = parseOrThrow(PropertyTestsArgsSchema, args);
    const contract = {
      function: parsed.functionName,
      inputs: parsed.inputs,
      outputs: parsed.outputs,
      invariants: parsed.invariants,
    };

    const testCases = await this.agent.generatePropertyTests(contract);
    
    let response = `# Property-Based Tests for ${args.functionName}\n\n`;
    response += `Generated ${testCases.length} property tests:\n\n`;
    
    for (const testCase of testCases) {
      response += `## ${testCase.name}\n`;
      response += `**Priority**: ${testCase.priority}\n`;
      response += `**Description**: ${testCase.description}\n`;
      response += `\n\`\`\`typescript\n${testCase.code}\n\`\`\`\n\n`;
      
      if (testCase.dataGenerators && testCase.dataGenerators.length > 0) {
        response += `**Data Generators**:\n`;
        for (const gen of testCase.dataGenerators) {
          response += `- ${gen.name}: ${gen.type} with constraints ${gen.constraints.join(', ')}\n`;
        }
        response += '\n';
      }
    }
    
    return {
      content: [{ type: 'text', text: response }],
    };
  }

  private async handleGenerateBDDScenarios(args: unknown) {
    const parsed: BDDArgs = parseOrThrow(BDDArgsSchema, args);
    const userStory = {
      title: parsed.title,
      asA: parsed.asA,
      iWant: parsed.iWant,
      soThat: parsed.soThat,
      acceptanceCriteria: parsed.acceptanceCriteria,
    };

    const gherkin = await this.agent.generateBDDScenarios(userStory);
    
    return {
      content: [
        {
          type: 'text',
          text: `# BDD Scenarios\n\n\`\`\`gherkin\n${gherkin}\n\`\`\``,
        },
      ],
    };
  }

  private async handlePlanIntegrationTests(args: unknown) {
    const parsed: PlanIntegrationArgs = parseOrThrow(PlanIntegrationArgsSchema, args);
    const architecture = {
      services: parsed.services,
      dataFlow: parsed.dataFlow,
    };

    const plan = await this.agent.planIntegrationTests(architecture);
    
    let response = `# Integration Test Plan\n\n`;
    response += `## Test Execution Order\n`;
    response += plan.testOrder.map((t, i) => `${i + 1}. ${t}`).join('\n');
    response += `\n\n`;
    
    response += `## Mock Strategy\n`;
    response += `Approach: ${plan.mockStrategy.approach}\n`;
    if (plan.mockStrategy.mocks.length > 0) {
      response += `Mocks needed:\n`;
      for (const mock of plan.mockStrategy.mocks) {
        response += `- ${mock.service}: ${mock.type}\n`;
      }
    }
    response += `\n`;
    
    response += `## Test Phases\n`;
    for (const phase of plan.testPlan.phases) {
      response += `### ${phase.name}\n`;
      response += `${phase.tests.length} tests planned\n\n`;
    }
    
    response += `**Coverage**: ${plan.testPlan.coverage}%\n`;
    
    return {
      content: [{ type: 'text', text: response }],
    };
  }

  private async handleGenerateSecurityTests(args: unknown) {
    const parsed: SecurityTestsArgs = parseOrThrow(SecurityTestsArgsSchema, args);
    const testCases = await this.agent.generateSecurityTests(parsed.endpoint);
    
    let response = `# Security Tests for ${parsed.endpoint.method} ${parsed.endpoint.path}\n\n`;
    response += `Generated ${testCases.length} security tests based on OWASP guidelines:\n\n`;
    
    for (const testCase of testCases) {
      response += `## ${testCase.name}\n`;
      response += `**Type**: ${testCase.type}\n`;
      response += `**Priority**: ${testCase.priority}\n`;
      response += `**Description**: ${testCase.description}\n`;
      response += `\n\`\`\`typescript\n${testCase.code}\n\`\`\`\n\n`;
    }
    
    return {
      content: [{ type: 'text', text: response }],
    };
  }

  private async handleDesignPerformanceTests(args: unknown) {
    const parsed: DesignPerformanceArgs = parseOrThrow(DesignPerformanceArgsSchema, args);
    const testSuite = await this.agent.designPerformanceTests(parsed.sla);
    
    let response = `# Performance Test Suite\n\n`;
    
    response += `## Load Tests\n`;
    for (const test of testSuite.loadTests) {
      response += `- **${test.name}**: ${test.users} users over ${test.duration}s\n`;
    }
    response += `\n`;
    
    response += `## Stress Tests\n`;
    for (const test of testSuite.stressTests) {
      response += `- **${test.name}**: Find breaking point with ${test.users} users\n`;
    }
    response += `\n`;
    
    response += `## Spike Tests\n`;
    for (const test of testSuite.spikeTests) {
      response += `- **${test.name}**: ${test.spikeMultiplier}x spike in traffic\n`;
    }
    response += `\n`;
    
    response += `## Soak Tests\n`;
    for (const test of testSuite.soakTests) {
      response += `- **${test.name}**: Sustained load for ${test.sustainedDuration}s\n`;
    }
    
    return {
      content: [{ type: 'text', text: response }],
    };
  }

  private async handleAnalyzeTestCoverage(args: unknown) {
    const _parsed: AnalyzeCoverageArgs = parseOrThrow(AnalyzeCoverageArgsSchema, args);
    // This would analyze actual project coverage
    const response = `# Test Coverage Analysis\n\n`;
    
    return {
      content: [
        {
          type: 'text',
          text: response + 'Coverage analysis would be performed on the actual project files.',
        },
      ],
    };
  }

  private formatTestGenerationResult(result: {
    testFile: string;
    testCases: { name: string; type: string; priority: string; description: string }[];
    coverage: {
      functional: unknown[];
      edgeCases: unknown[];
      errorHandling: unknown[];
      performance: unknown[];
      security: unknown[];
    };
    recommendations: string[];
    testContent: string;
  }): string {
    let response = `# Generated Tests\n\n`;
    response += `**Test File**: ${result.testFile}\n\n`;
    
    response += `## Test Cases (${result.testCases.length})\n\n`;
    for (const testCase of result.testCases) {
      response += `### ${testCase.name}\n`;
      response += `- **Type**: ${testCase.type}\n`;
      response += `- **Priority**: ${testCase.priority}\n`;
      response += `- **Description**: ${testCase.description}\n\n`;
    }
    
    response += `## Coverage Analysis\n`;
    response += `- **Functional**: ${result.coverage.functional.length} tests\n`;
    response += `- **Edge Cases**: ${result.coverage.edgeCases.length} tests\n`;
    response += `- **Error Handling**: ${result.coverage.errorHandling.length} tests\n`;
    response += `- **Performance**: ${result.coverage.performance.length} tests\n`;
    response += `- **Security**: ${result.coverage.security.length} tests\n\n`;
    
    if (result.recommendations.length > 0) {
      response += `## Recommendations\n`;
      for (const rec of result.recommendations) {
        response += `- ${rec}\n`;
      }
      response += '\n';
    }
    
    response += `## Generated Test Code\n\n`;
    response += `\`\`\`typescript\n${result.testContent}\n\`\`\``;
    
    return response;
  }

  async run() {
    const transport = new StdioServerTransport();
    await this.server.connect(transport);
  }
}

// Run the server
const server = new TestGenerationServer();
server.run().catch(console.error);
