/**
 * MCP Server for Code Generation Agent
 * Provides tools for Phase 4: Code generation from tests
 */

import { MCPServer, Tool, Request, Response } from '@modelcontextprotocol/sdk';
import { CodeGenerationAgent } from '../agents/code-generation-agent.js';

export class CodeGenerationServer extends MCPServer {
  private agent: CodeGenerationAgent;

  constructor() {
    super({
      name: 'ae-framework-code-generation',
      version: '1.0.0',
      description: 'Code generation from tests and specifications'
    });

    this.agent = new CodeGenerationAgent();
    this.registerTools();
  }

  private registerTools() {
    // Tool: Generate code from tests
    this.registerTool({
      name: 'generate_code_from_tests',
      description: 'Generate implementation code from test files (TDD approach)',
      parameters: {
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
            enum: ['typescript', 'javascript', 'python', 'go', 'rust']
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
      },
      handler: async (request: Request) => {
        const result = await this.agent.generateCodeFromTests(request.params);
        return {
          files: result.files,
          coverage: result.coverage,
          testResults: result.testResults,
          suggestions: result.suggestions
        };
      }
    });

    // Tool: Generate API from OpenAPI
    this.registerTool({
      name: 'generate_api_from_openapi',
      description: 'Generate API implementation from OpenAPI specification',
      parameters: {
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
      },
      handler: async (request: Request) => {
        const result = await this.agent.generateFromOpenAPI(
          request.params.spec,
          {
            framework: request.params.framework,
            database: request.params.database,
            includeValidation: request.params.includeValidation,
            includeAuth: request.params.includeAuth
          }
        );
        return result;
      }
    });

    // Tool: Apply design patterns
    this.registerTool({
      name: 'apply_design_patterns',
      description: 'Apply design patterns to existing code',
      parameters: {
        type: 'object',
        properties: {
          code: { type: 'string' },
          patterns: {
            type: 'array',
            items: {
              type: 'string',
              enum: ['singleton', 'factory', 'observer', 'strategy', 'decorator', 'repository']
            }
          }
        },
        required: ['code', 'patterns']
      },
      handler: async (request: Request) => {
        const result = await this.agent.applyDesignPatterns(
          request.params.code,
          request.params.patterns
        );
        return { code: result };
      }
    });

    // Tool: Optimize performance
    this.registerTool({
      name: 'optimize_performance',
      description: 'Optimize code for performance',
      parameters: {
        type: 'object',
        properties: {
          code: { type: 'string' },
          metrics: {
            type: 'object',
            properties: {
              targetResponseTime: { type: 'number' },
              targetMemoryUsage: { type: 'number' },
              targetCPUUsage: { type: 'number' }
            }
          }
        },
        required: ['code']
      },
      handler: async (request: Request) => {
        const result = await this.agent.optimizePerformance(
          request.params.code,
          request.params.metrics || {}
        );
        return result;
      }
    });

    // Tool: Add security features
    this.registerTool({
      name: 'add_security_features',
      description: 'Add security features to code',
      parameters: {
        type: 'object',
        properties: {
          code: { type: 'string' },
          requirements: {
            type: 'object',
            properties: {
              authentication: {
                type: 'string',
                enum: ['jwt', 'oauth', 'basic']
              },
              authorization: {
                type: 'string',
                enum: ['rbac', 'abac', 'simple']
              },
              encryption: { type: 'boolean' },
              rateLimit: { type: 'boolean' },
              cors: { type: 'boolean' }
            }
          }
        },
        required: ['code', 'requirements']
      },
      handler: async (request: Request) => {
        const result = await this.agent.addSecurityFeatures(
          request.params.code,
          request.params.requirements
        );
        return { code: result };
      }
    });

    // Tool: Generate error handling
    this.registerTool({
      name: 'generate_error_handling',
      description: 'Add comprehensive error handling to code',
      parameters: {
        type: 'object',
        properties: {
          code: { type: 'string' },
          strategy: {
            type: 'object',
            properties: {
              type: {
                type: 'string',
                enum: ['try-catch', 'result-type', 'middleware']
              },
              logging: { type: 'boolean' },
              recovery: { type: 'boolean' },
              userFriendly: { type: 'boolean' }
            },
            required: ['type']
          }
        },
        required: ['code', 'strategy']
      },
      handler: async (request: Request) => {
        const result = await this.agent.generateErrorHandling(
          request.params.code,
          request.params.strategy
        );
        return { code: result };
      }
    });

    // Tool: Generate data access layer
    this.registerTool({
      name: 'generate_data_access_layer',
      description: 'Generate database access layer with ORM',
      parameters: {
        type: 'object',
        properties: {
          schema: {
            type: 'object',
            properties: {
              tables: {
                type: 'array',
                items: {
                  type: 'object',
                  properties: {
                    name: { type: 'string' },
                    columns: { type: 'array' }
                  }
                }
              }
            }
          },
          orm: {
            type: 'string',
            enum: ['typeorm', 'prisma', 'sequelize', 'none']
          },
          database: {
            type: 'string',
            enum: ['postgres', 'mysql', 'mongodb', 'sqlite']
          },
          includeTransactions: { type: 'boolean' },
          includeMigrations: { type: 'boolean' }
        },
        required: ['schema', 'database']
      },
      handler: async (request: Request) => {
        const result = await this.agent.generateDataAccessLayer(
          request.params.schema,
          {
            orm: request.params.orm,
            database: request.params.database,
            includeTransactions: request.params.includeTransactions,
            includeMigrations: request.params.includeMigrations
          }
        );
        return result;
      }
    });

    // Tool: Refactor code
    this.registerTool({
      name: 'refactor_code',
      description: 'Refactor code to improve quality',
      parameters: {
        type: 'object',
        properties: {
          code: { type: 'string' },
          goals: {
            type: 'object',
            properties: {
              reduceComplexity: { type: 'boolean' },
              improveDRY: { type: 'boolean' },
              improveNaming: { type: 'boolean' },
              extractMethods: { type: 'boolean' },
              introducePatterns: {
                type: 'array',
                items: { type: 'string' }
              }
            }
          }
        },
        required: ['code', 'goals']
      },
      handler: async (request: Request) => {
        const result = await this.agent.refactorCode(
          request.params.code,
          request.params.goals
        );
        return result;
      }
    });

    // Tool: Validate against tests
    this.registerTool({
      name: 'validate_code_against_tests',
      description: 'Validate generated code against test suite',
      parameters: {
        type: 'object',
        properties: {
          codeFiles: {
            type: 'array',
            items: {
              type: 'object',
              properties: {
                path: { type: 'string' },
                content: { type: 'string' }
              }
            }
          },
          testFiles: {
            type: 'array',
            items: {
              type: 'object',
              properties: {
                path: { type: 'string' },
                content: { type: 'string' }
              }
            }
          }
        },
        required: ['codeFiles', 'testFiles']
      },
      handler: async (request: Request) => {
        // Run tests against code
        const results = await this.agent.runTests(
          request.params.codeFiles,
          request.params.testFiles
        );
        
        const coverage = this.agent.calculateCoverage(results);
        const suggestions = this.agent.generateSuggestions(results, coverage);
        
        return {
          testResults: results,
          coverage,
          suggestions,
          passing: results.every(r => r.status === 'passing')
        };
      }
    });

    // Tool: Suggest improvements
    this.registerTool({
      name: 'suggest_code_improvements',
      description: 'Analyze code and suggest improvements',
      parameters: {
        type: 'object',
        properties: {
          code: { type: 'string' },
          focus: {
            type: 'array',
            items: {
              type: 'string',
              enum: ['performance', 'security', 'maintainability', 'testability', 'documentation']
            }
          }
        },
        required: ['code']
      },
      handler: async (request: Request) => {
        const suggestions = [];
        const focus = request.params.focus || ['performance', 'security', 'maintainability'];
        
        for (const area of focus) {
          switch (area) {
            case 'performance':
              suggestions.push('Consider adding caching for expensive operations');
              suggestions.push('Use database indexes for frequent queries');
              break;
            case 'security':
              suggestions.push('Add input validation for all user inputs');
              suggestions.push('Implement rate limiting for API endpoints');
              break;
            case 'maintainability':
              suggestions.push('Extract complex logic into separate functions');
              suggestions.push('Add comprehensive logging');
              break;
            case 'testability':
              suggestions.push('Use dependency injection for better testability');
              suggestions.push('Avoid global state');
              break;
            case 'documentation':
              suggestions.push('Add JSDoc comments for public APIs');
              suggestions.push('Create README with usage examples');
              break;
          }
        }
        
        return { suggestions };
      }
    });
  }

  async start(port: number = 3004) {
    await this.listen(port);
    console.log(`Code Generation MCP Server running on port ${port}`);
  }
}

// Start server if run directly
if (import.meta.url === `file://${process.argv[1]}`) {
  const server = new CodeGenerationServer();
  server.start();
}