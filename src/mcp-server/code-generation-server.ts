/**
 * MCP Server for Code Generation Agent
 * Provides tools for Phase 4: Code generation from tests
 */

import { Server } from '@modelcontextprotocol/sdk/server/index.js';
import { StdioServerTransport } from '@modelcontextprotocol/sdk/server/stdio.js';
import { CallToolRequestSchema, ListToolsRequestSchema } from '@modelcontextprotocol/sdk/types.js';
import { CodeGenerationAgent } from '../agents/code-generation-agent.js';

export class CodeGenerationServer {
  private server: Server;
  private agent: CodeGenerationAgent;

  constructor() {
    this.server = new Server(
      {
        name: 'ae-framework-code-generation',
        version: '1.0.0',
      },
      {
        capabilities: {
          tools: {},
        },
      }
    );
    
    this.agent = new CodeGenerationAgent();
    this.registerTools();
    this.setupErrorHandling();
  }

  private setupErrorHandling() {
    this.server.onerror = (error) => {
      console.error('[MCP Error]', error);
    };

    process.on('SIGINT', async () => {
      await this.server.close();
      process.exit(0);
    });
  }

  private registerTools() {
    // Set up list tools handler
    this.server.setRequestHandler(ListToolsRequestSchema, async () => {
      return {
        tools: [
          {
            name: 'generate_code_from_tests',
            description: 'Generate implementation code from test files (TDD approach)',
            inputSchema: {
              type: 'object',
              properties: {
                tests: {
                  type: 'array',
                  items: {
                    type: 'object',
                    properties: {
                      path: { type: 'string' },
                      content: { type: 'string' },
                      type: { 
                        type: 'string', 
                        enum: ['unit', 'integration', 'e2e'] 
                      }
                    },
                    required: ['path', 'content', 'type']
                  }
                },
                language: {
                  type: 'string',
                  enum: ['typescript', 'javascript', 'python', 'go', 'rust', 'elixir']
                },
                framework: { type: 'string' },
                architecture: {
                  type: 'object',
                  properties: {
                    pattern: {
                      type: 'string',
                      enum: ['mvc', 'hexagonal', 'clean', 'ddd', 'microservice']
                    }
                  }
                }
              },
              required: ['tests', 'language']
            }
          },
          {
            name: 'generate_api_from_openapi',
            description: 'Generate API implementation from OpenAPI specification',
            inputSchema: {
              type: 'object',
              properties: {
                spec: { type: 'string' },
                framework: {
                  type: 'string',
                  enum: ['fastify', 'express', 'koa']
                },
                database: {
                  type: 'string',
                  enum: ['postgres', 'mongodb', 'mysql']
                },
                includeValidation: { type: 'boolean' },
                includeAuth: { type: 'boolean' }
              },
              required: ['spec', 'framework']
            }
          },
          {
            name: 'validate_code_against_tests',
            description: 'Validate generated code against test suite',
            inputSchema: {
              type: 'object',
              properties: {
                codeFiles: {
                  type: 'array',
                  items: {
                    type: 'object',
                    properties: {
                      path: { type: 'string' },
                      content: { type: 'string' }
                    },
                    required: ['path', 'content']
                  }
                },
                testFiles: {
                  type: 'array',
                  items: {
                    type: 'object',
                    properties: {
                      path: { type: 'string' },
                      content: { type: 'string' }
                    },
                    required: ['path', 'content']
                  }
                }
              },
              required: ['codeFiles', 'testFiles']
            }
          }
        ]
      };
    });

    // Set up call tool handler
    this.server.setRequestHandler(CallToolRequestSchema, async (request) => {
      try {
        switch (request.params.name) {
          case 'generate_code_from_tests': {
            const args = request.params.arguments;
            if (!args) {
              throw new Error('Missing arguments for generate_code_from_tests');
            }
            const result = await this.agent.generateCodeFromTests(args as any);
            return {
              content: [
                {
                  type: 'text',
                  text: JSON.stringify({
                    files: result.files,
                    coverage: result.coverage,
                    testResults: result.testResults,
                    suggestions: result.suggestions
                  }, null, 2)
                }
              ]
            };
          }

          case 'generate_api_from_openapi': {
            const args = request.params.arguments as any;
            const result = await this.agent.generateFromOpenAPI(
              args.spec,
              {
                framework: args.framework,
                database: args.database,
                includeValidation: args.includeValidation,
                includeAuth: args.includeAuth
              }
            );
            return {
              content: [
                {
                  type: 'text',
                  text: JSON.stringify(result, null, 2)
                }
              ]
            };
          }

          case 'validate_code_against_tests': {
            const args = request.params.arguments as any;
            const results = await this.validateCodeAgainstTests(args.codeFiles, args.testFiles);
            return {
              content: [
                {
                  type: 'text',
                  text: JSON.stringify(results, null, 2)
                }
              ]
            };
          }

          default:
            throw new Error(`Unknown tool: ${request.params.name}`);
        }
      } catch (error) {
        return {
          content: [
            {
              type: 'text',
              text: JSON.stringify({
                error: error instanceof Error ? error.message : 'Unknown error',
                toolName: request.params.name
              }, null, 2)
            }
          ],
          isError: true
        };
      }
    });
  }

  private async validateCodeAgainstTests(codeFiles: any[], testFiles: any[]): Promise<any> {
    // Basic validation implementation
    console.log(`Validating ${codeFiles.length} code files against ${testFiles.length} test files`);
    
    return {
      testResults: testFiles.map(test => ({
        file: test.path,
        status: 'pending',
        coverage: 0
      })),
      coverage: {
        percentage: 0,
        details: {
          lines: { covered: 0, total: 0 },
          functions: { covered: 0, total: 0 },
          branches: { covered: 0, total: 0 }
        }
      },
      suggestions: [
        'Run actual test suite to get real coverage data',
        'Consider adding more integration tests'
      ],
      passing: false
    };
  }

  async start() {
    const transport = new StdioServerTransport();
    await this.server.connect(transport);
    console.log('Code Generation MCP Server started');
  }

  async stop() {
    await this.server.close();
  }
}

// Start server if run directly
if (typeof require !== 'undefined' && require.main === module) {
  const server = new CodeGenerationServer();
  server.start().catch(console.error);
}