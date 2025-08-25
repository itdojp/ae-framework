/**
 * Health Check Endpoint for ae-framework
 * Phase 1.4: Docker production optimization health checks
 */
import { FastifyInstance } from 'fastify';
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
export declare function registerHealthEndpoint(fastify: FastifyInstance): Promise<void>;
