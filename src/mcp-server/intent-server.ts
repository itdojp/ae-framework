#!/usr/bin/env node

/**
 * MCP Server for Intent Agent
 * Exposes Intent Agent capabilities as MCP tools for Phase 1 of ae-framework
 */

import { Server } from '@modelcontextprotocol/sdk/server/index.js';
import { StdioServerTransport } from '@modelcontextprotocol/sdk/server/stdio.js';
import {
  CallToolRequestSchema,
  ErrorCode,
  ListToolsRequestSchema,
  McpError,
} from '@modelcontextprotocol/sdk/types.js';
import { IntentAgent, IntentAnalysisRequest, RequirementSource, ProjectContext } from '../agents/intent-agent.js';

class IntentMCPServer {
  private server: Server;
  private agent: IntentAgent;

  constructor() {
    this.server = new Server(
      {
        name: 'intent-agent-server',
        version: '1.0.0',
      },
      {
        capabilities: {
          tools: {},
        },
      }
    );
    
    this.agent = new IntentAgent();
    this.setupHandlers();
  }

  private setupHandlers() {
    this.server.setRequestHandler(ListToolsRequestSchema, async () => {
      return {
        tools: [
          {
            name: 'analyze_intent',
            description: 'Analyze requirements and extract intent from multiple sources',
            inputSchema: {
              type: 'object',
              properties: {
                sources: {
                  type: 'array',
                  items: {
                    type: 'object',
                    properties: {
                      type: {
                        type: 'string',
                        enum: ['text', 'document', 'conversation', 'issue', 'email', 'diagram'],
                        description: 'Type of requirement source'
                      },
                      content: {
                        type: 'string',
                        description: 'Content of the requirement source'
                      },
                      metadata: {
                        type: 'object',
                        properties: {
                          author: { type: 'string' },
                          date: { type: 'string' },
                          priority: {
                            type: 'string',
                            enum: ['critical', 'high', 'medium', 'low']
                          },
                          tags: {
                            type: 'array',
                            items: { type: 'string' }
                          },
                          references: {
                            type: 'array',
                            items: { type: 'string' }
                          }
                        }
                      }
                    },
                    required: ['type', 'content']
                  }
                },
                context: {
                  type: 'object',
                  properties: {
                    domain: { type: 'string' },
                    existingSystem: { type: 'boolean' },
                    constraints: {
                      type: 'array',
                      items: {
                        type: 'object',
                        properties: {
                          type: {
                            type: 'string',
                            enum: ['technical', 'business', 'regulatory', 'resource']
                          },
                          description: { type: 'string' },
                          impact: {
                            type: 'string',
                            enum: ['high', 'medium', 'low']
                          }
                        },
                        required: ['type', 'description', 'impact']
                      }
                    },
                    stakeholders: {
                      type: 'array',
                      items: {
                        type: 'object',
                        properties: {
                          name: { type: 'string' },
                          role: { type: 'string' },
                          concerns: {
                            type: 'array',
                            items: { type: 'string' }
                          },
                          influenceLevel: {
                            type: 'string',
                            enum: ['high', 'medium', 'low']
                          }
                        },
                        required: ['name', 'role', 'concerns', 'influenceLevel']
                      }
                    },
                    glossary: {
                      type: 'array',
                      items: {
                        type: 'object',
                        properties: {
                          term: { type: 'string' },
                          definition: { type: 'string' },
                          context: { type: 'string' }
                        },
                        required: ['term', 'definition']
                      }
                    }
                  },
                  required: ['domain']
                },
                analysisDepth: {
                  type: 'string',
                  enum: ['basic', 'detailed', 'comprehensive'],
                  default: 'detailed'
                },
                outputFormat: {
                  type: 'string',
                  enum: ['structured', 'narrative', 'both'],
                  default: 'structured'
                }
              },
              required: ['sources']
            }
          },
          {
            name: 'extract_from_natural_language',
            description: 'Extract requirements from natural language text',
            inputSchema: {
              type: 'object',
              properties: {
                text: {
                  type: 'string',
                  description: 'Natural language text to extract requirements from'
                }
              },
              required: ['text']
            }
          },
          {
            name: 'create_user_stories',
            description: 'Generate user stories from requirements',
            inputSchema: {
              type: 'object',
              properties: {
                requirements: {
                  type: 'array',
                  items: {
                    type: 'object',
                    properties: {
                      id: { type: 'string' },
                      type: {
                        type: 'string',
                        enum: ['functional', 'non-functional', 'business', 'technical']
                      },
                      category: { type: 'string' },
                      description: { type: 'string' },
                      rationale: { type: 'string' },
                      priority: {
                        type: 'string',
                        enum: ['must', 'should', 'could', 'wont']
                      },
                      source: { type: 'string' },
                      status: {
                        type: 'string',
                        enum: ['draft', 'reviewed', 'approved', 'implemented']
                      }
                    },
                    required: ['id', 'type', 'category', 'description', 'priority', 'source', 'status']
                  }
                }
              },
              required: ['requirements']
            }
          },
          {
            name: 'build_domain_model',
            description: 'Build domain model with entities, relationships, bounded contexts, and aggregates',
            inputSchema: {
              type: 'object',
              properties: {
                requirements: {
                  type: 'array',
                  items: {
                    type: 'object',
                    properties: {
                      id: { type: 'string' },
                      type: {
                        type: 'string',
                        enum: ['functional', 'non-functional', 'business', 'technical']
                      },
                      category: { type: 'string' },
                      description: { type: 'string' },
                      priority: {
                        type: 'string',
                        enum: ['must', 'should', 'could', 'wont']
                      },
                      source: { type: 'string' },
                      status: {
                        type: 'string',
                        enum: ['draft', 'reviewed', 'approved', 'implemented']
                      }
                    },
                    required: ['id', 'type', 'category', 'description', 'priority', 'source', 'status']
                  }
                },
                context: {
                  type: 'object',
                  properties: {
                    domain: { type: 'string' },
                    existingSystem: { type: 'boolean' },
                    glossary: {
                      type: 'array',
                      items: {
                        type: 'object',
                        properties: {
                          term: { type: 'string' },
                          definition: { type: 'string' },
                          context: { type: 'string' }
                        },
                        required: ['term', 'definition']
                      }
                    }
                  }
                }
              },
              required: ['requirements']
            }
          },
          {
            name: 'detect_ambiguities',
            description: 'Detect and analyze ambiguities in requirement sources',
            inputSchema: {
              type: 'object',
              properties: {
                sources: {
                  type: 'array',
                  items: {
                    type: 'object',
                    properties: {
                      type: {
                        type: 'string',
                        enum: ['text', 'document', 'conversation', 'issue', 'email', 'diagram']
                      },
                      content: { type: 'string' },
                      metadata: {
                        type: 'object',
                        properties: {
                          author: { type: 'string' },
                          date: { type: 'string' }
                        }
                      }
                    },
                    required: ['type', 'content']
                  }
                }
              },
              required: ['sources']
            }
          },
          {
            name: 'validate_completeness',
            description: 'Validate requirements completeness and coverage',
            inputSchema: {
              type: 'object',
              properties: {
                requirements: {
                  type: 'array',
                  items: {
                    type: 'object',
                    properties: {
                      id: { type: 'string' },
                      category: { type: 'string' },
                      description: { type: 'string' }
                    },
                    required: ['id', 'category', 'description']
                  }
                }
              },
              required: ['requirements']
            }
          },
          {
            name: 'generate_specification_templates',
            description: 'Generate specification templates (Gherkin, OpenAPI, AsyncAPI, GraphQL)',
            inputSchema: {
              type: 'object',
              properties: {
                requirements: {
                  type: 'array',
                  items: {
                    type: 'object',
                    properties: {
                      id: { type: 'string' },
                      type: {
                        type: 'string',
                        enum: ['functional', 'non-functional', 'business', 'technical']
                      },
                      description: { type: 'string' }
                    },
                    required: ['id', 'type', 'description']
                  }
                }
              },
              required: ['requirements']
            }
          },
          {
            name: 'prioritize_requirements',
            description: 'Prioritize requirements using MoSCoW method',
            inputSchema: {
              type: 'object',
              properties: {
                requirements: {
                  type: 'array',
                  items: {
                    type: 'object',
                    properties: {
                      id: { type: 'string' },
                      description: { type: 'string' },
                      priority: {
                        type: 'string',
                        enum: ['must', 'should', 'could', 'wont']
                      }
                    },
                    required: ['id', 'description', 'priority']
                  }
                },
                constraints: {
                  type: 'array',
                  items: {
                    type: 'object',
                    properties: {
                      type: {
                        type: 'string',
                        enum: ['technical', 'business', 'regulatory', 'resource']
                      },
                      description: { type: 'string' },
                      impact: {
                        type: 'string',
                        enum: ['high', 'medium', 'low']
                      }
                    },
                    required: ['type', 'description', 'impact']
                  }
                }
              },
              required: ['requirements', 'constraints']
            }
          },
          {
            name: 'generate_acceptance_criteria',
            description: 'Generate acceptance criteria for a requirement',
            inputSchema: {
              type: 'object',
              properties: {
                requirement: {
                  type: 'object',
                  properties: {
                    id: { type: 'string' },
                    type: {
                      type: 'string',
                      enum: ['functional', 'non-functional', 'business', 'technical']
                    },
                    description: { type: 'string' }
                  },
                  required: ['id', 'type', 'description']
                }
              },
              required: ['requirement']
            }
          },
          {
            name: 'analyze_stakeholder_concerns',
            description: 'Analyze stakeholder concerns and identify conflicts',
            inputSchema: {
              type: 'object',
              properties: {
                stakeholders: {
                  type: 'array',
                  items: {
                    type: 'object',
                    properties: {
                      name: { type: 'string' },
                      role: { type: 'string' },
                      concerns: {
                        type: 'array',
                        items: { type: 'string' }
                      },
                      influenceLevel: {
                        type: 'string',
                        enum: ['high', 'medium', 'low']
                      }
                    },
                    required: ['name', 'role', 'concerns', 'influenceLevel']
                  }
                },
                requirements: {
                  type: 'array',
                  items: {
                    type: 'object',
                    properties: {
                      id: { type: 'string' },
                      description: { type: 'string' }
                    },
                    required: ['id', 'description']
                  }
                }
              },
              required: ['stakeholders', 'requirements']
            }
          }
        ]
      };
    });

    this.server.setRequestHandler(CallToolRequestSchema, async (request) => {
      const { name, arguments: args } = request.params;

      try {
        switch (name) {
          case 'analyze_intent':
            return await this.handleAnalyzeIntent(args as any);
          
          case 'extract_from_natural_language':
            return await this.handleExtractFromNaturalLanguage(args as any);
          
          case 'create_user_stories':
            return await this.handleCreateUserStories(args as any);
          
          case 'build_domain_model':
            return await this.handleBuildDomainModel(args as any);
          
          case 'detect_ambiguities':
            return await this.handleDetectAmbiguities(args as any);
          
          case 'validate_completeness':
            return await this.handleValidateCompleteness(args as any);
          
          case 'generate_specification_templates':
            return await this.handleGenerateSpecificationTemplates(args as any);
          
          case 'prioritize_requirements':
            return await this.handlePrioritizeRequirements(args as any);
          
          case 'generate_acceptance_criteria':
            return await this.handleGenerateAcceptanceCriteria(args as any);
          
          case 'analyze_stakeholder_concerns':
            return await this.handleAnalyzeStakeholderConcerns(args as any);
          
          default:
            throw new McpError(ErrorCode.MethodNotFound, `Unknown tool: ${name}`);
        }
      } catch (error) {
        throw new McpError(
          ErrorCode.InternalError,
          `Error executing ${name}: ${error instanceof Error ? error.message : String(error)}`
        );
      }
    });
  }

  private async handleAnalyzeIntent(args: {
    sources: RequirementSource[];
    context?: ProjectContext;
    analysisDepth?: 'basic' | 'detailed' | 'comprehensive';
    outputFormat?: 'structured' | 'narrative' | 'both';
  }) {
    const request: IntentAnalysisRequest = {
      sources: args.sources,
      context: args.context,
      analysisDepth: args.analysisDepth || 'detailed',
      outputFormat: args.outputFormat || 'structured',
    };

    const result = await this.agent.analyzeIntent(request);
    
    return {
      content: [
        {
          type: 'text' as const,
          text: JSON.stringify(result, null, 2),
        },
      ],
    };
  }

  private async handleExtractFromNaturalLanguage(args: { text: string }) {
    const requirements = await this.agent.extractFromNaturalLanguage(args.text);
    
    return {
      content: [
        {
          type: 'text' as const,
          text: JSON.stringify({
            extracted_requirements: requirements,
            count: requirements.length,
          }, null, 2),
        },
      ],
    };
  }

  private async handleCreateUserStories(args: { requirements: any[] }) {
    const userStories = await this.agent.createUserStories(args.requirements);
    
    return {
      content: [
        {
          type: 'text' as const,
          text: JSON.stringify({
            user_stories: userStories,
            count: userStories.length,
          }, null, 2),
        },
      ],
    };
  }

  private async handleBuildDomainModel(args: { requirements: any[]; context?: ProjectContext }) {
    const domainModel = await this.agent.buildDomainModelFromRequirements(
      args.requirements,
      args.context
    );
    
    return {
      content: [
        {
          type: 'text' as const,
          text: JSON.stringify({
            domain_model: domainModel,
            summary: {
              entities: domainModel.entities.length,
              relationships: domainModel.relationships.length,
              bounded_contexts: domainModel.boundedContexts.length,
              aggregates: domainModel.aggregates.length,
            },
          }, null, 2),
        },
      ],
    };
  }

  private async handleDetectAmbiguities(args: { sources: RequirementSource[] }) {
    const ambiguities = await this.agent.detectAmbiguities(args.sources);
    
    return {
      content: [
        {
          type: 'text' as const,
          text: JSON.stringify({
            ambiguities,
            count: ambiguities.length,
            severity_breakdown: {
              high: ambiguities.filter(a => a.severity === 'high').length,
              medium: ambiguities.filter(a => a.severity === 'medium').length,
              low: ambiguities.filter(a => a.severity === 'low').length,
            },
          }, null, 2),
        },
      ],
    };
  }

  private async handleValidateCompleteness(args: { requirements: any[] }) {
    const validation = await this.agent.validateCompleteness(args.requirements);
    
    return {
      content: [
        {
          type: 'text' as const,
          text: JSON.stringify({
            validation_result: validation,
            recommendations: validation.missing.length > 0 
              ? `Consider adding requirements for: ${validation.missing.join(', ')}`
              : 'Requirements coverage is complete',
          }, null, 2),
        },
      ],
    };
  }

  private async handleGenerateSpecificationTemplates(args: { requirements: any[] }) {
    const templates = await this.agent.generateSpecificationTemplates(args.requirements);
    
    return {
      content: [
        {
          type: 'text' as const,
          text: JSON.stringify({
            specification_templates: templates,
            summary: {
              gherkin_scenarios: templates.gherkin.length,
              openapi_spec: 'Generated',
              asyncapi_spec: 'Generated',
              graphql_schema: 'Generated',
            },
          }, null, 2),
        },
      ],
    };
  }

  private async handlePrioritizeRequirements(args: { requirements: any[]; constraints: any[] }) {
    const prioritized = await this.agent.prioritizeRequirements(
      args.requirements,
      args.constraints
    );
    
    return {
      content: [
        {
          type: 'text' as const,
          text: JSON.stringify({
            prioritized_requirements: prioritized,
            priority_distribution: {
              must: prioritized.filter(r => r.priority === 'must').length,
              should: prioritized.filter(r => r.priority === 'should').length,
              could: prioritized.filter(r => r.priority === 'could').length,
              wont: prioritized.filter(r => r.priority === 'wont').length,
            },
          }, null, 2),
        },
      ],
    };
  }

  private async handleGenerateAcceptanceCriteria(args: { requirement: any }) {
    const criteria = await this.agent.generateAcceptanceCriteria(args.requirement);
    
    return {
      content: [
        {
          type: 'text' as const,
          text: JSON.stringify({
            acceptance_criteria: criteria,
            requirement_id: args.requirement.id,
            criteria_count: criteria.length,
          }, null, 2),
        },
      ],
    };
  }

  private async handleAnalyzeStakeholderConcerns(args: { stakeholders: any[]; requirements: any[] }) {
    const analysis = await this.agent.analyzeStakeholderConcerns(
      args.stakeholders,
      args.requirements
    );
    
    // Convert Map objects to plain objects for JSON serialization
    const addressedObj = Object.fromEntries(analysis.addressed);
    const unaddressedObj = Object.fromEntries(analysis.unaddressed);
    
    return {
      content: [
        {
          type: 'text' as const,
          text: JSON.stringify({
            stakeholder_analysis: {
              addressed_concerns: addressedObj,
              unaddressed_concerns: unaddressedObj,
              conflicts: analysis.conflicts,
            },
            summary: {
              total_stakeholders: args.stakeholders.length,
              total_conflicts: analysis.conflicts.length,
              stakeholders_with_unaddressed_concerns: Object.keys(unaddressedObj).filter(
                key => unaddressedObj[key].length > 0
              ).length,
            },
          }, null, 2),
        },
      ],
    };
  }

  async run() {
    const transport = new StdioServerTransport();
    await this.server.connect(transport);
    console.error('Intent Agent MCP server running on stdio');
  }
}

const server = new IntentMCPServer();
server.run().catch(console.error);