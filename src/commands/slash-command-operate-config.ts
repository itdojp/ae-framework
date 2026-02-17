import type { OperateAgentConfig } from '../agents/operate-agent.js';

export function createDefaultOperateAgentConfig(): OperateAgentConfig {
  return {
    deploymentConfig: {
      cicdProvider: 'github-actions',
      environments: ['dev', 'prod'],
      rolloutStrategy: 'rolling',
      healthCheckUrl: 'http://localhost:3000/health',
      timeoutSeconds: 300,
    },
    monitoringConfig: {
      metricsEndpoint: 'http://localhost:8080/metrics',
      logsEndpoint: 'http://localhost:8080/logs',
      tracesEndpoint: 'http://localhost:8080/traces',
      healthEndpoints: ['http://localhost:3000/health'],
      checkIntervalMs: 30000,
    },
    alertingConfig: {
      channels: [],
      thresholds: [],
      escalationPolicy: [],
    },
    scalingConfig: {
      minInstances: 1,
      maxInstances: 10,
      targetCpuPercent: 80,
      targetMemoryPercent: 80,
      scaleUpCooldown: '5m',
      scaleDownCooldown: '10m',
    },
    securityConfig: {
      scanSchedule: '0 2 * * *',
      vulnerabilityThreshold: 'medium',
      complianceFrameworks: [],
      securityEndpoints: [],
    },
    costConfig: {
      budgetLimit: 10000,
      costCenter: 'development',
      optimizationTargets: [],
      reportingSchedule: 'weekly',
    },
    sloConfig: {
      availability: 99.9,
      latencyP95Ms: 200,
      errorRatePercent: 0.1,
      throughputRps: 1000,
      evaluationWindow: '1d',
    },
    chaosConfig: {
      enabled: false,
      schedule: '0 3 * * 1',
      experiments: [],
      safetyLimits: {
        maxErrorRate: 5,
        maxLatencyMs: 5000,
        minHealthyInstances: 1,
      },
    },
  };
}
