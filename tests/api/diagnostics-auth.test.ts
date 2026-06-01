import { describe, expect, it } from 'vitest';
import type { FastifyInstance } from 'fastify';
import { formatGWT } from '../utils/gwt-format';
import { createServer } from '../../src/api/server.js';

const closeApp = async (app: FastifyInstance) => {
  await app.close();
};

describe('diagnostic endpoint authorization', () => {
  it(
    formatGWT(
      'anonymous diagnostics request',
      'GET /health/detailed and /api/runtime-guard/stats',
      'fails closed when no admin diagnostics token is configured',
    ),
    async () => {
      const app = await createServer();
      await app.ready();

      try {
        const detailed = await app.inject({ method: 'GET', url: '/health/detailed' });
        const stats = await app.inject({ method: 'GET', url: '/api/runtime-guard/stats' });

        expect(detailed.statusCode).toBe(403);
        expect(JSON.parse(detailed.body)).toEqual(expect.objectContaining({
          error: 'DIAGNOSTICS_DISABLED',
        }));
        expect(stats.statusCode).toBe(403);
        expect(JSON.parse(stats.body)).toEqual(expect.objectContaining({
          error: 'DIAGNOSTICS_DISABLED',
        }));
      } finally {
        await closeApp(app);
      }
    },
  );

  it(
    formatGWT(
      'public liveness request',
      'GET /health and /alive',
      'returns only minimal unauthenticated health data',
    ),
    async () => {
      const app = await createServer();
      await app.ready();

      try {
        const health = await app.inject({ method: 'GET', url: '/health' });
        const alive = await app.inject({ method: 'GET', url: '/alive' });

        expect(health.statusCode).toBe(200);
        expect(JSON.parse(health.body)).toEqual(expect.objectContaining({
          status: 'healthy',
          service: 'ae-framework-api',
          timestamp: expect.any(String),
        }));

        expect(alive.statusCode).toBe(200);
        const aliveBody = JSON.parse(alive.body);
        expect(aliveBody).toEqual({
          status: 'alive',
          timestamp: expect.any(String),
        });
        expect(aliveBody).not.toHaveProperty('pid');
        expect(aliveBody).not.toHaveProperty('argv');
      } finally {
        await closeApp(app);
      }
    },
  );

  it(
    formatGWT(
      'configured admin diagnostics token',
      'GET /health/detailed and /api/runtime-guard/stats',
      'requires the token and avoids process argument disclosure',
    ),
    async () => {
      const app = await createServer({ adminDiagnosticsToken: 'diagnostics-secret' });
      await app.ready();

      try {
        const missing = await app.inject({ method: 'GET', url: '/health/detailed' });
        const wrong = await app.inject({
          method: 'GET',
          url: '/api/runtime-guard/stats',
          headers: { authorization: 'Bearer wrong-secret' },
        });
        const detailed = await app.inject({
          method: 'GET',
          url: '/health/detailed',
          headers: { 'x-ae-admin-token': 'diagnostics-secret' },
        });
        const stats = await app.inject({
          method: 'GET',
          url: '/api/runtime-guard/stats',
          headers: { authorization: 'Bearer diagnostics-secret' },
        });

        expect(missing.statusCode).toBe(401);
        expect(missing.headers['www-authenticate']).toContain('Bearer');
        expect(wrong.statusCode).toBe(401);

        expect(detailed.statusCode).toBe(200);
        const detailedBody = JSON.parse(detailed.body);
        expect(detailedBody.detailed.process).toEqual(expect.objectContaining({
          uptimeSeconds: expect.any(Number),
          nodeVersion: expect.any(String),
          platform: expect.any(String),
        }));
        expect(detailedBody.detailed.process).not.toHaveProperty('argv');
        expect(detailedBody.detailed.process).not.toHaveProperty('pid');
        expect(detailedBody.detailed.process).not.toHaveProperty('ppid');
        expect(detailedBody.detailed.process).not.toHaveProperty('title');

        expect(stats.statusCode).toBe(200);
        expect(JSON.parse(stats.body)).toEqual(expect.objectContaining({
          violations: expect.any(Object),
          timestamp: expect.any(String),
        }));
      } finally {
        await closeApp(app);
      }
    },
  );
});
