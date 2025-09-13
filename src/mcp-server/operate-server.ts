#!/usr/bin/env node

import { Server } from '@modelcontextprotocol/sdk/server/index.js';
import { StdioServerTransport } from '@modelcontextprotocol/sdk/server/stdio.js';
import {
  CallToolRequestSchema,
  ErrorCode,
  ListToolsRequestSchema,
  McpError,
} from '@modelcontextprotocol/sdk/types.js';
import { z } from 'zod';
import {
  OperateAgent,
  type OperateAgentConfig,
  type DeploymentParams,
  type LogAnalysisParams,
  type IncidentParams,
  type PerformanceOptimizationParams,
  type ScalingParams,
  type ChaosTestParams,
  type CostAnalysisParams,
  type SecurityScanParams,
} from '../agents/operate-agent.js';

// Tool parameter schemas
const DeployApplicationSchema = z.object({
  environment: z.string().min(1, 'Environment is required'),
  version: z.string().min(1, 'Version is required'),
  strategy: z.enum(['blue-green', 'canary', 'rolling']).optional(),
  rollbackOnFailure: z.boolean().default(false),
  healthCheckTimeout: z.number().positive().optional(),
});

const AnalyzeLogsSchema = z.object({
  startTime: z.string().refine(date => !isNaN(Date.parse(date)), 'Invalid start time'),
  endTime: z.string().refine(date => !isNaN(Date.parse(date)), 'Invalid end time'),
  logLevel: z.enum(['debug', 'info', 'warn', 'error']).optional(),
  service: z.string().optional(),
  query: z.string().optional(),
});

const ManageIncidentSchema = z.object({
  action: z.enum(['create', 'update', 'resolve', 'escalate']),
  incidentId: z.string().optional(),
  title: z.string().optional(),
  description: z.string().optional(),
  severity: z.enum(['low', 'medium', 'high', 'critical']).optional(),
  assignee: z.string().optional(),
  updateNotes: z.string().optional(),
  resolution: z.string().optional(),
});

const OptimizePerformanceSchema = z.object({
  service: z.string().optional(),
  timeWindow: z.string().min(1, 'Time window is required'),
  metrics: z.array(z.string()).min(1, 'At least one metric is required'),
  autoApply: z.boolean().default(false),
});

const ScaleResourcesSchema = z.object({
  service: z.string().min(1, 'Service is required'),
  action: z.enum(['auto', 'scale-up', 'scale-down']).optional(),
  targetInstances: z.number().int().positive().optional(),
  force: z.boolean().default(false),
});

const RunChaosTestSchema = z.object({
  experiment: z.string().min(1, 'Experiment name is required'),
  dryRun: z.boolean().default(false),
  duration: z.string().optional(),
  intensity: z.number().min(0).max(100).optional(),
});

const AnalyzeCostsSchema = z.object({
  timeWindow: z.string().min(1, 'Time window is required'),
  services: z.array(z.string()).optional(),
  includePredictions: z.boolean().default(false),
});

const SecurityScanSchema = z.object({
  scope: z.enum(['infrastructure', 'application', 'dependencies', 'all']).default('all'),
  includeCompliance: z.boolean().default(true),
  frameworks: z.array(z.string()).optional(),
});

/**
 * MCP Server for the Operate Agent
 * 
 * This server provides tools for production operations, monitoring, and optimization:
 * - Deployment orchestration (CI/CD integration)
 * - Infrastructure monitoring and alerting
 * - Performance monitoring and optimization
 * - Log aggregation and analysis
 * - Incident response and management
 * - Capacity planning and scaling
 * - Security monitoring and compliance
 * - Cost optimization
 * - Chaos engineering and resilience testing
 * - SLO/SLA tracking
 */
class OperateServer {
  private server: Server;
  private operateAgent: OperateAgent;

  constructor() {
    this.server = new Server(
      {
        name: 'operate-server',
        version: '1.0.0',
      },
      {
        capabilities: {
          tools: {},
        },
      }
    );

    // Initialize with default configuration - in production, this would come from environment/config
    const defaultConfig: OperateAgentConfig = {
      deploymentConfig: {
        cicdProvider: 'github-actions',
        environments: ['staging', 'production'],
        rolloutStrategy: 'blue-green',
        healthCheckUrl: 'http://localhost:3000/health',
        timeoutSeconds: 300,
      },
      monitoringConfig: {
        metricsEndpoint: 'http://localhost:9090',
        logsEndpoint: 'http://localhost:3100',
        tracesEndpoint: 'http://localhost:16686',
        healthEndpoints: ['http://localhost:3000/health'],
        checkIntervalMs: 30000,
      },
      alertingConfig: {
        channels: [
          {
            type: 'slack',
            endpoint: 'https://hooks.slack.com/services/...',
            severity: 'high',
          },
        ],
        thresholds: [
          {
            metric: 'error_rate',
            condition: 'gt',
            value: 5,
            duration: '5m',
            severity: 'high',
          },
        ],
        escalationPolicy: [
          {
            delay: '10m',
            channels: ['slack', 'pagerduty'],
          },
        ],
      },
      scalingConfig: {
        minInstances: 1,
        maxInstances: 10,
        targetCpuPercent: 70,
        targetMemoryPercent: 80,
        scaleUpCooldown: '2m',
        scaleDownCooldown: '5m',
      },
      securityConfig: {
        scanSchedule: '0 2 * * *', // Daily at 2 AM
        vulnerabilityThreshold: 'medium',
        complianceFrameworks: ['SOC2', 'PCI-DSS'],
        securityEndpoints: ['http://localhost:8080/security'],
      },
      costConfig: {
        budgetLimit: 10000,
        costCenter: 'engineering',
        optimizationTargets: ['compute', 'storage', 'network'],
        reportingSchedule: '0 9 * * MON', // Weekly Monday at 9 AM
      },
      sloConfig: {
        availability: 99.9,
        latencyP95Ms: 200,
        errorRatePercent: 0.1,
        throughputRps: 1000,
        evaluationWindow: '24h',
      },
      chaosConfig: {
        enabled: true,
        schedule: '0 14 * * FRI', // Weekly Friday at 2 PM
        experiments: [
          {
            name: 'pod-failure-test',
            type: 'pod-failure',
            targets: ['api-service'],
            duration: '5m',
            intensity: 10,
          },
        ],
        safetyLimits: {
          maxErrorRate: 10,
          maxLatencyMs: 1000,
          minHealthyInstances: 1,
        },
      },
    };

    this.operateAgent = new OperateAgent(defaultConfig);
    this.setupHandlers();
  }

  private setupHandlers() {
    this.server.setRequestHandler(ListToolsRequestSchema, async () => {
      return {
        tools: [
          {
            name: 'deploy_application',
            description: 'Orchestrate application deployment with various strategies (blue-green, canary, rolling)',
            inputSchema: {
              type: 'object',
              properties: {
                environment: {
                  type: 'string',
                  description: 'Target deployment environment (e.g., staging, production)',
                },
                version: {
                  type: 'string',
                  description: 'Application version to deploy',
                },
                strategy: {
                  type: 'string',
                  enum: ['blue-green', 'canary', 'rolling'],
                  description: 'Deployment strategy to use',
                },
                rollbackOnFailure: {
                  type: 'boolean',
                  description: 'Whether to automatically rollback on deployment failure',
                  default: false,
                },
                healthCheckTimeout: {
                  type: 'number',
                  description: 'Health check timeout in seconds',
                },
              },
              required: ['environment', 'version'],
            },
          },
          {
            name: 'monitor_health',
            description: 'Check system health across all monitored endpoints',
            inputSchema: {
              type: 'object',
              properties: {},
            },
          },
          {
            name: 'analyze_logs',
            description: 'Analyze aggregated logs for patterns, anomalies, and insights',
            inputSchema: {
              type: 'object',
              properties: {
                startTime: {
                  type: 'string',
                  description: 'Start time for log analysis (ISO 8601 format)',
                },
                endTime: {
                  type: 'string',
                  description: 'End time for log analysis (ISO 8601 format)',
                },
                logLevel: {
                  type: 'string',
                  enum: ['debug', 'info', 'warn', 'error'],
                  description: 'Minimum log level to analyze',
                },
                service: {
                  type: 'string',
                  description: 'Specific service to analyze logs for',
                },
                query: {
                  type: 'string',
                  description: 'Search query to filter logs',
                },
              },
              required: ['startTime', 'endTime'],
            },
          },
          {
            name: 'manage_incident',
            description: 'Handle incident lifecycle - create, update, resolve, or escalate incidents',
            inputSchema: {
              type: 'object',
              properties: {
                action: {
                  type: 'string',
                  enum: ['create', 'update', 'resolve', 'escalate'],
                  description: 'Incident management action to perform',
                },
                incidentId: {
                  type: 'string',
                  description: 'Incident ID (required for update, resolve, escalate actions)',
                },
                title: {
                  type: 'string',
                  description: 'Incident title (required for create action)',
                },
                description: {
                  type: 'string',
                  description: 'Incident description (required for create action)',
                },
                severity: {
                  type: 'string',
                  enum: ['low', 'medium', 'high', 'critical'],
                  description: 'Incident severity level',
                },
                assignee: {
                  type: 'string',
                  description: 'Person assigned to the incident',
                },
                updateNotes: {
                  type: 'string',
                  description: 'Update notes (for update action)',
                },
                resolution: {
                  type: 'string',
                  description: 'Resolution details (for resolve action)',
                },
              },
              required: ['action'],
            },
          },
          {
            name: 'optimize_performance',
            description: 'Analyze performance metrics and apply optimization recommendations',
            inputSchema: {
              type: 'object',
              properties: {
                service: {
                  type: 'string',
                  description: 'Specific service to optimize (optional, defaults to all)',
                },
                timeWindow: {
                  type: 'string',
                  description: 'Time window for analysis (e.g., "1h", "24h", "7d")',
                },
                metrics: {
                  type: 'array',
                  items: { type: 'string' },
                  description: 'Performance metrics to analyze (e.g., ["cpu", "memory", "latency"])',
                },
                autoApply: {
                  type: 'boolean',
                  description: 'Whether to automatically apply low-risk optimizations',
                  default: false,
                },
              },
              required: ['timeWindow', 'metrics'],
            },
          },
          {
            name: 'scale_resources',
            description: 'Manage resource scaling based on demand and performance metrics',
            inputSchema: {
              type: 'object',
              properties: {
                service: {
                  type: 'string',
                  description: 'Service to scale',
                },
                action: {
                  type: 'string',
                  enum: ['auto', 'scale-up', 'scale-down'],
                  description: 'Scaling action to perform',
                },
                targetInstances: {
                  type: 'number',
                  description: 'Target number of instances (for manual scaling)',
                },
                force: {
                  type: 'boolean',
                  description: 'Force scaling operation even if it exceeds safety limits',
                  default: false,
                },
              },
              required: ['service'],
            },
          },
          {
            name: 'run_chaos_test',
            description: 'Execute chaos engineering experiments to test system resilience',
            inputSchema: {
              type: 'object',
              properties: {
                experiment: {
                  type: 'string',
                  description: 'Name of the chaos experiment to run',
                },
                dryRun: {
                  type: 'boolean',
                  description: 'Run in dry-run mode without actually causing disruption',
                  default: false,
                },
                duration: {
                  type: 'string',
                  description: 'Duration of the experiment (e.g., "5m", "10m")',
                },
                intensity: {
                  type: 'number',
                  minimum: 0,
                  maximum: 100,
                  description: 'Intensity of the chaos experiment (0-100)',
                },
              },
              required: ['experiment'],
            },
          },
          {
            name: 'track_slo',
            description: 'Monitor SLO/SLA compliance and generate status reports',
            inputSchema: {
              type: 'object',
              properties: {},
            },
          },
          {
            name: 'analyze_costs',
            description: 'Analyze infrastructure costs and generate optimization recommendations',
            inputSchema: {
              type: 'object',
              properties: {
                timeWindow: {
                  type: 'string',
                  description: 'Time window for cost analysis (e.g., "1d", "7d", "30d")',
                },
                services: {
                  type: 'array',
                  items: { type: 'string' },
                  description: 'Specific services to analyze (optional, defaults to all)',
                },
                includePredictions: {
                  type: 'boolean',
                  description: 'Include cost predictions and forecasts',
                  default: false,
                },
              },
              required: ['timeWindow'],
            },
          },
          {
            name: 'security_scan',
            description: 'Run security scans and compliance checks across infrastructure and applications',
            inputSchema: {
              type: 'object',
              properties: {
                scope: {
                  type: 'string',
                  enum: ['infrastructure', 'application', 'dependencies', 'all'],
                  description: 'Scope of the security scan',
                  default: 'all',
                },
                includeCompliance: {
                  type: 'boolean',
                  description: 'Include compliance framework checks',
                  default: true,
                },
                frameworks: {
                  type: 'array',
                  items: { type: 'string' },
                  description: 'Specific compliance frameworks to check (e.g., ["SOC2", "PCI-DSS"])',
                },
              },
            },
          },
        ],
      };
    });

    this.server.setRequestHandler(CallToolRequestSchema, async (request) => {
      try {
        const { name, arguments: args } = request.params;

        switch (name) {
          case 'deploy_application': {
            const params = DeployApplicationSchema.parse(args);
            const deploymentParams: DeploymentParams = {
              environment: params.environment,
              version: params.version,
              ...(params.strategy !== undefined ? { strategy: params.strategy } : {}),
              ...(params.rollbackOnFailure !== undefined ? { rollbackOnFailure: params.rollbackOnFailure } : {}),
              ...(params.healthCheckTimeout !== undefined ? { healthCheckTimeout: params.healthCheckTimeout } : {}),
            };
            const result = await this.operateAgent.deployApplication(deploymentParams);
            return {
              content: [
                {
                  type: 'text',
                  text: JSON.stringify(result, null, 2),
                },
              ],
            };
          }

          case 'monitor_health': {
            const result = await this.operateAgent.monitorHealth();
            return {
              content: [
                {
                  type: 'text',
                  text: JSON.stringify(result, null, 2),
                },
              ],
            };
          }

          case 'analyze_logs': {
            const params = AnalyzeLogsSchema.parse(args);
            const logParams: LogAnalysisParams = {
              startTime: new Date(params.startTime),
              endTime: new Date(params.endTime),
              ...(params.logLevel !== undefined ? { logLevel: params.logLevel } : {}),
              ...(params.service !== undefined ? { service: params.service } : {}),
              ...(params.query !== undefined ? { query: params.query } : {}),
            };
            const result = await this.operateAgent.analyzeLogs(logParams);
            return {
              content: [
                {
                  type: 'text',
                  text: JSON.stringify(result, null, 2),
                },
              ],
            };
          }

          case 'manage_incident': {
            const params = ManageIncidentSchema.parse(args);
            const incidentParams: IncidentParams = {
              action: params.action,
              ...(params.incidentId !== undefined ? { incidentId: params.incidentId } : {}),
              ...(params.title !== undefined ? { title: params.title } : {}),
              ...(params.description !== undefined ? { description: params.description } : {}),
              ...(params.severity !== undefined ? { severity: params.severity } : {}),
              ...(params.assignee !== undefined ? { assignee: params.assignee } : {}),
              ...(params.updateNotes !== undefined ? { updateNotes: params.updateNotes } : {}),
              ...(params.resolution !== undefined ? { resolution: params.resolution } : {}),
            };
            const result = await this.operateAgent.manageIncident(incidentParams);
            return {
              content: [
                {
                  type: 'text',
                  text: JSON.stringify(result, null, 2),
                },
              ],
            };
          }

          case 'optimize_performance': {
            const params = OptimizePerformanceSchema.parse(args);
            const optimizationParams: PerformanceOptimizationParams = {
              timeWindow: params.timeWindow,
              metrics: params.metrics,
              ...(params.service !== undefined ? { service: params.service } : {}),
              ...(params.autoApply !== undefined ? { autoApply: params.autoApply } : {}),
            };
            const result = await this.operateAgent.optimizePerformance(optimizationParams);
            return {
              content: [
                {
                  type: 'text',
                  text: JSON.stringify(result, null, 2),
                },
              ],
            };
          }

          case 'scale_resources': {
            const params = ScaleResourcesSchema.parse(args);
            const scalingParams: ScalingParams = {
              service: params.service,
              ...(params.action !== undefined ? { action: params.action } : {}),
              ...(params.targetInstances !== undefined ? { targetInstances: params.targetInstances } : {}),
              ...(params.force !== undefined ? { force: params.force } : {}),
            };
            const result = await this.operateAgent.scaleResources(scalingParams);
            return {
              content: [
                {
                  type: 'text',
                  text: JSON.stringify(result, null, 2),
                },
              ],
            };
          }

          case 'run_chaos_test': {
            const params = RunChaosTestSchema.parse(args);
            const chaosParams: ChaosTestParams = {
              experiment: params.experiment,
              ...(params.dryRun !== undefined ? { dryRun: params.dryRun } : {}),
              ...(params.duration !== undefined ? { duration: params.duration } : {}),
              ...(params.intensity !== undefined ? { intensity: params.intensity } : {}),
            };
            const result = await this.operateAgent.runChaosTest(chaosParams);
            return {
              content: [
                {
                  type: 'text',
                  text: JSON.stringify(result, null, 2),
                },
              ],
            };
          }

          case 'track_slo': {
            const result = await this.operateAgent.trackSlo();
            return {
              content: [
                {
                  type: 'text',
                  text: JSON.stringify(result, null, 2),
                },
              ],
            };
          }

          case 'analyze_costs': {
            const params = AnalyzeCostsSchema.parse(args);
            const costParams: CostAnalysisParams = {
              timeWindow: params.timeWindow,
              ...(params.services !== undefined ? { services: params.services } : {}),
              ...(params.includePredictions !== undefined ? { includePredictions: params.includePredictions } : {}),
            };
            const result = await this.operateAgent.analyzeCosts(costParams);
            return {
              content: [
                {
                  type: 'text',
                  text: JSON.stringify(result, null, 2),
                },
              ],
            };
          }

          case 'security_scan': {
            const params = SecurityScanSchema.parse(args);
            const scanParams: SecurityScanParams = {
              ...(params.scope !== undefined ? { scope: params.scope } : {}),
              ...(params.includeCompliance !== undefined ? { includeCompliance: params.includeCompliance } : {}),
              ...(params.frameworks !== undefined ? { frameworks: params.frameworks } : {}),
            };
            const result = await this.operateAgent.securityScan(scanParams);
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
            throw new McpError(
              ErrorCode.MethodNotFound,
              `Unknown tool: ${name}`
            );
        }
      } catch (error) {
        if (error instanceof z.ZodError) {
          throw new McpError(
            ErrorCode.InvalidParams,
            `Invalid parameters: ${error.message}`
          );
        }
        throw error;
      }
    });
  }

  async run() {
    const transport = new StdioServerTransport();
    await this.server.connect(transport);
    console.error('Operate MCP server running on stdio');
  }
}

const server = new OperateServer();
server.run().catch(console.error);
