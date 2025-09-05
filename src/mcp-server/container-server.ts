/**
 * Container MCP Server - Phase 3 of Issue #37
 * MCP server providing container-based verification tools
 */

import { Server } from '@modelcontextprotocol/sdk/server/index.js';
import { StdioServerTransport } from '@modelcontextprotocol/sdk/server/stdio.js';
import {
  CallToolRequestSchema,
  ListToolsRequestSchema,
  Tool,
} from '@modelcontextprotocol/sdk/types.js';
import { ContainerAgent, ContainerAgentConfig } from '../agents/container-agent.js';
import {
  BuildVerificationImageArgsSchema,
  CancelJobArgsSchema,
  CleanupArgsSchema,
  GetJobStatusArgsSchema,
  ListJobsArgsSchema,
  RunContainerVerificationArgsSchema,
  parseOrThrow,
  type BuildVerificationImageArgs,
  type CancelJobArgs,
  type CleanupArgs,
  type GetJobStatusArgs,
  type ListJobsArgs,
  type RunContainerVerificationArgs,
} from './schemas.js';

export class ContainerServer {
  private server: Server;
  private agent: ContainerAgent;

  constructor(config: ContainerAgentConfig = {}) {
    this.server = new Server({
      name: 'ae-framework-container-server',
      version: '1.0.0',
    }, {
      capabilities: {
        tools: {},
      },
    });

    this.agent = new ContainerAgent(config);
    this.setupTools();
    this.setupErrorHandling();
  }

  private setupTools(): void {
    // Tool definitions
    const tools: Tool[] = [
      {
        name: 'initialize_container_system',
        description: 'Initialize the container-based verification system',
        inputSchema: {
          type: 'object',
          properties: {},
          additionalProperties: false,
        },
      },
      {
        name: 'run_container_verification',
        description: 'Run verification in containerized environment',
        inputSchema: {
          type: 'object',
          properties: {
            projectPath: {
              type: 'string',
              description: 'Path to the project to verify',
            },
            language: {
              type: 'string',
              enum: ['rust', 'elixir', 'multi'],
              description: 'Programming language for verification',
            },
            tools: {
              type: 'array',
              items: { type: 'string' },
              description: 'Verification tools to use',
            },
            jobName: {
              type: 'string',
              description: 'Optional name for the verification job',
            },
            timeout: {
              type: 'number',
              description: 'Timeout in seconds for verification',
            },
            buildImages: {
              type: 'boolean',
              description: 'Whether to build verification images if needed',
              default: false,
            },
            environment: {
              type: 'object',
              additionalProperties: { type: 'string' },
              description: 'Additional environment variables',
            },
          },
          required: ['projectPath', 'language', 'tools'],
          additionalProperties: false,
        },
      },
      {
        name: 'build_verification_image',
        description: 'Build container image for verification environment',
        inputSchema: {
          type: 'object',
          properties: {
            language: {
              type: 'string',
              enum: ['rust', 'elixir', 'multi'],
              description: 'Programming language for the verification image',
            },
            tools: {
              type: 'array',
              items: { type: 'string' },
              description: 'Verification tools to include in the image',
            },
            baseImage: {
              type: 'string',
              description: 'Base container image to build from',
            },
            tag: {
              type: 'string',
              description: 'Tag for the built image',
            },
            push: {
              type: 'boolean',
              description: 'Whether to push the image to a registry',
              default: false,
            },
            buildArgs: {
              type: 'object',
              additionalProperties: { type: 'string' },
              description: 'Build arguments for container build',
            },
          },
          required: ['language', 'tools'],
          additionalProperties: false,
        },
      },
      {
        name: 'get_verification_job_status',
        description: 'Get status of a specific verification job',
        inputSchema: {
          type: 'object',
          properties: {
            jobId: {
              type: 'string',
              description: 'ID of the verification job',
            },
          },
          required: ['jobId'],
          additionalProperties: false,
        },
      },
      {
        name: 'list_verification_jobs',
        description: 'List verification jobs with optional filtering',
        inputSchema: {
          type: 'object',
          properties: {
            status: {
              type: 'string',
              enum: ['pending', 'running', 'completed', 'failed'],
              description: 'Filter by job status',
            },
            language: {
              type: 'string',
              enum: ['rust', 'elixir', 'multi'],
              description: 'Filter by programming language',
            },
          },
          additionalProperties: false,
        },
      },
      {
        name: 'cancel_verification_job',
        description: 'Cancel a running verification job',
        inputSchema: {
          type: 'object',
          properties: {
            jobId: {
              type: 'string',
              description: 'ID of the verification job to cancel',
            },
          },
          required: ['jobId'],
          additionalProperties: false,
        },
      },
      {
        name: 'get_container_system_status',
        description: 'Get overall status of the container verification system',
        inputSchema: {
          type: 'object',
          properties: {},
          additionalProperties: false,
        },
      },
      {
        name: 'cleanup_container_resources',
        description: 'Cleanup old containers and verification resources',
        inputSchema: {
          type: 'object',
          properties: {
            maxAge: {
              type: 'number',
              description: 'Maximum age of resources to keep in seconds',
              default: 3600,
            },
            keepCompleted: {
              type: 'number',
              description: 'Number of completed jobs to keep',
              default: 10,
            },
            force: {
              type: 'boolean',
              description: 'Force cleanup even if resources are in use',
              default: false,
            },
          },
          additionalProperties: false,
        },
      },
      {
        name: 'list_container_engines',
        description: 'List available container engines (Docker, Podman, etc.)',
        inputSchema: {
          type: 'object',
          properties: {},
          additionalProperties: false,
        },
      },
      {
        name: 'shutdown_container_system',
        description: 'Shutdown the container verification system',
        inputSchema: {
          type: 'object',
          properties: {},
          additionalProperties: false,
        },
      },
    ];

    // Register list tools handler
    this.server.setRequestHandler(ListToolsRequestSchema, async () => ({
      tools,
    }));

    // Register call tool handler
    this.server.setRequestHandler(CallToolRequestSchema, async (request) => {
      const { name, arguments: args } = request.params;

      try {
        switch (name) {
          case 'initialize_container_system': {
            const result = await this.agent.initialize();
            return {
              content: [
                {
                  type: 'text',
                  text: JSON.stringify(result, null, 2),
                },
              ],
            };
          }

          case 'run_container_verification': {
            const parsed: RunContainerVerificationArgs = parseOrThrow(RunContainerVerificationArgsSchema, args);
            const result = await this.agent.runVerification(parsed as any);
            return {
              content: [
                {
                  type: 'text',
                  text: JSON.stringify(result, null, 2),
                },
              ],
            };
          }

          case 'build_verification_image': {
            const parsed: BuildVerificationImageArgs = parseOrThrow(BuildVerificationImageArgsSchema, args);
            const result = await this.agent.buildVerificationImage(parsed as any);
            return {
              content: [
                {
                  type: 'text',
                  text: JSON.stringify(result, null, 2),
                },
              ],
            };
          }

          case 'get_verification_job_status': {
            const { jobId }: GetJobStatusArgs = parseOrThrow(GetJobStatusArgsSchema, args);
            const result = await this.agent.getJobStatus(jobId);
            return {
              content: [
                {
                  type: 'text',
                  text: JSON.stringify(result, null, 2),
                },
              ],
            };
          }

          case 'list_verification_jobs': {
            const parsed: ListJobsArgs = parseOrThrow(ListJobsArgsSchema, args);
            const result = await this.agent.listJobs(parsed as any);
            return {
              content: [
                {
                  type: 'text',
                  text: JSON.stringify(result, null, 2),
                },
              ],
            };
          }

          case 'cancel_verification_job': {
            const { jobId }: CancelJobArgs = parseOrThrow(CancelJobArgsSchema, args);
            const result = await this.agent.cancelJob(jobId);
            return {
              content: [
                {
                  type: 'text',
                  text: JSON.stringify(result, null, 2),
                },
              ],
            };
          }

          case 'get_container_system_status': {
            const result = await this.agent.getStatus();
            return {
              content: [
                {
                  type: 'text',
                  text: JSON.stringify(result, null, 2),
                },
              ],
            };
          }

          case 'cleanup_container_resources': {
            const parsed: CleanupArgs = parseOrThrow(CleanupArgsSchema, args);
            const result = await this.agent.cleanup(parsed as any);
            return {
              content: [
                {
                  type: 'text',
                  text: JSON.stringify(result, null, 2),
                },
              ],
            };
          }

          case 'list_container_engines': {
            const result = await this.agent.listEngines();
            return {
              content: [
                {
                  type: 'text',
                  text: JSON.stringify(result, null, 2),
                },
              ],
            };
          }

          case 'shutdown_container_system': {
            const result = await this.agent.shutdown();
            return {
              content: [
                {
                  type: 'text',
                  text: JSON.stringify(result, null, 2),
                },
              ],
            };
          }

          default:
            throw new Error(`Unknown tool: ${name}`);
        }
      } catch (error: unknown) {
        return {
          content: [
            {
              type: 'text',
              text: JSON.stringify({
                success: false,
                message: `Tool execution failed: ${error instanceof Error ? error.message : String(error)}`,
                error: error instanceof Error ? error.message : String(error),
                tool: name,
                args,
              }, null, 2),
            },
          ],
        };
      }
    });
  }

  private setupErrorHandling(): void {
    this.server.onerror = (error) => {
      console.error('Container MCP Server error:', error);
    };

    process.on('SIGINT', async () => {
      console.log('🛑 Shutting down Container MCP Server...');
      try {
        await this.agent.shutdown();
        await this.server.close();
        process.exit(0);
      } catch (error) {
        console.error('Error during shutdown:', error);
        process.exit(1);
      }
    });
  }

  async start(): Promise<void> {
    const transport = new StdioServerTransport();
    await this.server.connect(transport);
    console.error('🐋 Container MCP Server started successfully');
  }
}

// CLI entry point
if (import.meta.url === `file://${process.argv[1]}`) {
  const server = new ContainerServer();
  server.start().catch((error) => {
    console.error('Failed to start Container MCP Server:', error);
    process.exit(1);
  });
}
