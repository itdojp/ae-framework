/**
 * Health Check Endpoint for ae-framework
 * Phase 1.4: Docker production optimization health checks
 */

import type { FastifyInstance, FastifyReply, FastifyRequest } from 'fastify';
import { telemetryService } from '../telemetry/telemetry-service.js';
import { readFileSync } from 'fs';
import { fileURLToPath } from 'url';
import { dirname, join } from 'path';

// Read version from package.json at startup
const __filename = fileURLToPath(import.meta.url);
const __dirname = dirname(__filename);
const packageJsonPath = join(__dirname, '../../package.json');
let APP_VERSION = '1.0.0';
try {
  const packageJson = JSON.parse(readFileSync(packageJsonPath, 'utf8'));
  APP_VERSION = packageJson.version || '1.0.0';
} catch (error) {
  console.warn('Failed to read version from package.json, using default:', APP_VERSION);
}

export interface HealthStatus {
  status: 'healthy' | 'unhealthy' | 'degraded';
  timestamp: string;
  uptime: number;
  version: string;
  environment: string;
  checks: {
    memory: {
      status: 'ok' | 'warning' | 'critical';
      used: number;
      total: number;
      percentage: number;
    };
    system: {
      status: 'ok' | 'error';
      nodeVersion: string;
      platform: string;
    };
    telemetry: {
      status: 'ok' | 'error';
      message: string;
    };
  };
}

export async function registerHealthEndpoint(fastify: FastifyInstance): Promise<void> {
  // Simple health check endpoint
  fastify.get('/health', async (request: FastifyRequest, reply: FastifyReply) => {
    const healthStatus = await getHealthStatus();
    
    const httpStatus = healthStatus.status === 'healthy' ? 200 :
                       healthStatus.status === 'degraded' ? 200 : 503;
    
    reply.status(httpStatus).send(healthStatus);
  });

  // Detailed health check for monitoring
  fastify.get('/health/detailed', async (request: FastifyRequest, reply: FastifyReply) => {
    const healthStatus = await getDetailedHealthStatus();
    
    const httpStatus = healthStatus.status === 'healthy' ? 200 :
                       healthStatus.status === 'degraded' ? 200 : 503;
    
    reply.status(httpStatus).send(healthStatus);
  });

  // Readiness probe for Kubernetes/Docker orchestration
  fastify.get('/ready', async (request: FastifyRequest, reply: FastifyReply) => {
    // Check if application is ready to serve traffic
    const isReady = await checkReadiness();
    
    if (isReady) {
      reply.status(200).send({ status: 'ready', timestamp: new Date().toISOString() });
    } else {
      reply.status(503).send({ status: 'not ready', timestamp: new Date().toISOString() });
    }
  });

  // Liveness probe for Kubernetes/Docker orchestration
  fastify.get('/alive', async (request: FastifyRequest, reply: FastifyReply) => {
    // Simple liveness check - if we can respond, we're alive
    reply.status(200).send({ 
      status: 'alive', 
      timestamp: new Date().toISOString(),
      pid: process.pid
    });
  });
}

async function getHealthStatus(): Promise<HealthStatus> {
  const memoryUsage = process.memoryUsage();
  const totalMemory = memoryUsage.heapTotal + memoryUsage.external + memoryUsage.arrayBuffers;
  const usedMemory = memoryUsage.heapUsed;
  const memoryPercentage = (usedMemory / totalMemory) * 100;

  const memoryStatus = memoryPercentage > 90 ? 'critical' :
                       memoryPercentage > 70 ? 'warning' : 'ok';

  let telemetryStatus = 'ok';
  let telemetryMessage = 'Telemetry service available';
  
  try {
    // Test telemetry service
    const tracer = telemetryService.getTracer();
    if (!tracer) {
      telemetryStatus = 'error';
      telemetryMessage = 'Telemetry tracer not available';
    }
  } catch (error) {
    telemetryStatus = 'error';
    telemetryMessage = `Telemetry error: ${error instanceof Error ? error.message : 'Unknown error'}`;
  }

  const systemStatus = 'ok'; // Basic system check

  const overallStatus = memoryStatus === 'critical' || telemetryStatus === 'error' ? 'unhealthy' :
                        memoryStatus === 'warning' ? 'degraded' : 'healthy';

  return {
    status: overallStatus,
    timestamp: new Date().toISOString(),
    uptime: process.uptime(),
    version: APP_VERSION,
    environment: process.env.NODE_ENV || 'development',
    checks: {
      memory: {
        status: memoryStatus,
        used: usedMemory,
        total: totalMemory,
        percentage: Math.round(memoryPercentage)
      },
      system: {
        status: systemStatus,
        nodeVersion: process.version,
        platform: process.platform
      },
      telemetry: {
        status: telemetryStatus as 'ok' | 'error',
        message: telemetryMessage
      }
    }
  };
}

async function getDetailedHealthStatus(): Promise<HealthStatus & { 
  detailed: {
    process: {
      pid: number;
      ppid: number;
      title: string;
      argv: string[];
    };
    memory: {
      rss: number;
      heapTotal: number;
      heapUsed: number;
      external: number;
      arrayBuffers: number;
    };
    cpu: {
      usage: NodeJS.CpuUsage;
    };
  }
}> {
  const basicHealth = await getHealthStatus();
  const memoryUsage = process.memoryUsage();
  const cpuUsage = process.cpuUsage();

  return {
    ...basicHealth,
    detailed: {
      process: {
        pid: process.pid,
        ppid: process.ppid,
        title: process.title,
        argv: process.argv
      },
      memory: memoryUsage,
      cpu: {
        usage: cpuUsage
      }
    }
  };
}

async function checkReadiness(): Promise<boolean> {
  try {
    // Check if critical services are available
    // For ae-framework, check if telemetry service is working
    const tracer = telemetryService.getTracer();
    if (!tracer) {
      return false;
    }

    // Check memory usage
    const memoryUsage = process.memoryUsage();
    const totalMemory = memoryUsage.heapTotal + memoryUsage.external + memoryUsage.arrayBuffers;
    const usedMemory = memoryUsage.heapUsed;
    const memoryPercentage = (usedMemory / totalMemory) * 100;
    
    // Not ready if memory usage is too high
    if (memoryPercentage > 95) {
      return false;
    }

    return true;
  } catch (error) {
    return false;
  }
}