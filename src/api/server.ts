import Fastify, { FastifyInstance } from "fastify";
import { Reservation } from "../domain/contracts.js";
import { securityHeadersPlugin, getSecurityConfiguration } from "./middleware/security-headers.js";
import { runtimeGuard, CommonSchemas } from "../telemetry/runtime-guards.js";
import { enhancedTelemetry, TELEMETRY_ATTRIBUTES } from "../telemetry/enhanced-telemetry.js";
import { trace } from '@opentelemetry/api';
import { registerHealthEndpoint } from '../health/health-endpoint.js';

/**
 * Create and configure Fastify server instance
 */
export async function createServer(): Promise<FastifyInstance> {
  const app = Fastify({ 
    logger: true,
    genReqId: () => `req_${Date.now()}_${Math.random().toString(36).substring(2, 11)}`,
  });

  const tracer = trace.getTracer('ae-framework-api');

  // Register security headers middleware with development config for testing
  const securityConfig = process.env.NODE_ENV === 'test' 
    ? { enabled: true } // Use defaults with everything enabled for testing
    : getSecurityConfiguration();
  await app.register(securityHeadersPlugin, securityConfig);

  // Add request tracing hook
  app.addHook('onRequest', async (request, reply) => {
    const span = tracer.startSpan(`${request.method} ${request.url}`, {
      attributes: {
        [TELEMETRY_ATTRIBUTES.REQUEST_ID]: request.id,
        [TELEMETRY_ATTRIBUTES.SERVICE_COMPONENT]: 'api-server',
        [TELEMETRY_ATTRIBUTES.SERVICE_OPERATION]: `${request.method} ${request.url}`,
        'http.method': request.method,
        'http.url': request.url,
        'http.user_agent': request.headers['user-agent'] || 'unknown',
      },
    });
    
    (request as any).span = span;
    (request as any).startTime = Date.now();
    enhancedTelemetry.recordCounter('api.requests.total', 1, {
      method: request.method,
      endpoint: request.url,
    });
  });

  // Add response timing hook
  app.addHook('onResponse', async (request, reply) => {
    const span = (request as any).span;
    if (span) {
      span.setAttributes({
        'http.status_code': reply.statusCode,
        [TELEMETRY_ATTRIBUTES.DURATION_MS]: Date.now() - (request as any).startTime || 0,
      });
      
      if (reply.statusCode >= 400) {
        span.recordException(new Error(`HTTP ${reply.statusCode}`));
      }
      
      span.end();
    }

    enhancedTelemetry.recordCounter('api.responses.total', 1, {
      method: request.method,
      endpoint: request.url,
      status_code: reply.statusCode.toString(),
    });
  });

  // Health check endpoint with response validation
  app.get("/health", async (req, reply) => {
    const timer = enhancedTelemetry.createTimer('api.health_check.duration');
    
    try {
      const healthData = { 
        status: "healthy" as const, 
        timestamp: new Date().toISOString(),
        service: "ae-framework-api"
      };

      // Validate response against schema
      const validation = runtimeGuard.validateResponse(
        CommonSchemas.HealthResponse,
        healthData,
        {
          requestId: req.id,
          endpoint: 'GET /health',
          statusCode: 200,
        }
      );

      if (!validation.valid) {
        console.error('Health check response validation failed:', validation.violations);
        // Still return the data in case of validation error to maintain availability
      }

      const duration = timer.end({
        endpoint: '/health',
        validation_result: validation.valid ? 'success' : 'failure',
      });

      enhancedTelemetry.recordQualityMetrics({
        score: validation.valid ? 100 : 0,
        component: 'health-check',
        phase: 'runtime',
      });

      return reply.code(200).send(healthData);
    } catch (error) {
      timer.end({ endpoint: '/health', result: 'error' });
      const span = (req as any).span;
      if (span) {
        span.recordException(error as Error);
      }
      throw error;
    }
  });

  // Reservations endpoint with full validation
  app.post("/reservations", async (req, reply) => {
    const timer = enhancedTelemetry.createTimer('api.reservations.duration');
    
    try {
      // Validate request payload
      const requestValidation = runtimeGuard.validateRequest(
        CommonSchemas.ReservationRequest,
        req.body,
        {
          requestId: req.id,
          endpoint: 'POST /reservations',
          operation: 'create_reservation',
        }
      );

      if (!requestValidation.valid) {
        const violation = requestValidation.violations?.[0];
        timer.end({ 
          endpoint: '/reservations', 
          result: 'validation_error',
          violation_type: violation?.type || 'unknown',
        });
        
        return reply.code(400).send({
          error: "VALIDATION_ERROR",
          message: "Request payload validation failed",
          details: violation?.details || 'Validation failed',
          violation_id: violation?.id || 'unknown',
        });
      }

      const { orderId, itemId, quantity } = requestValidation.data!;

      // Business rule validation
      if (quantity > 100) {
        runtimeGuard.recordBusinessRuleViolation(
          'max_quantity_limit',
          `Quantity ${quantity} exceeds maximum allowed (100)`,
          'medium' as any,
          { orderId, itemId, quantity }
        );
        
        timer.end({ endpoint: '/reservations', result: 'business_rule_violation' });
        
        return reply.code(400).send({
          error: "BUSINESS_RULE_VIOLATION",
          message: "Quantity exceeds maximum allowed limit of 100",
        });
      }

      // TODO: service 層に委譲（在庫確認・冪等処理・トランザクション）
      const responseData = { ok: true };

      // Validate response
      const responseValidation = runtimeGuard.validateResponse(
        CommonSchemas.ReservationResponse,
        responseData,
        {
          requestId: req.id,
          endpoint: 'POST /reservations',
          statusCode: 201,
        }
      );

      if (!responseValidation.valid) {
        console.error('Reservation response validation failed:', responseValidation.violations);
      }

      const duration = timer.end({
        endpoint: '/reservations',
        result: 'success',
        validation_result: responseValidation.valid ? 'success' : 'failure',
      });

      enhancedTelemetry.recordQualityMetrics({
        score: responseValidation.valid ? 100 : 0,
        component: 'reservations',
        phase: 'runtime',
      });

      return reply.code(201).send(responseData);
    } catch (error) {
      timer.end({ endpoint: '/reservations', result: 'error' });
      const span = (req as any).span;
      if (span) {
        span.recordException(error as Error);
      }
      throw error;
    }
  });

  // Runtime guard statistics endpoint
  app.get("/api/runtime-guard/stats", async (req, reply) => {
    try {
      const stats = runtimeGuard.getViolationStats();
      return reply.code(200).send({
        violations: stats,
        uptime: process.uptime(),
        timestamp: new Date().toISOString(),
      });
    } catch (error) {
      const span = (req as any).span;
      if (span) {
        span.recordException(error as Error);
      }
      throw error;
    }
  });

  // Register health check endpoints for Docker/Kubernetes
  await registerHealthEndpoint(app);

  return app;
}

// Export a function to get a configured server instance for backward compatibility
export default async function getServer() {
  return createServer();
}