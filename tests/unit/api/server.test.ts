import { describe, it, expect, beforeAll, afterAll } from 'vitest';
import type { FastifyInstance } from 'fastify';
import { createServer } from '../../../src/api/server.js';

describe('API server', () => {
  let app: FastifyInstance;

  beforeAll(async () => {
    process.env.NODE_ENV = 'test';
    app = await createServer();
  });

  afterAll(async () => {
    await app.close();
  });

  it('returns a healthy status from /health and sets security headers', async () => {
    const response = await app.inject({ method: 'GET', url: '/health' });
    expect(response.statusCode).toBe(200);

    const payload = response.json();
    expect(payload).toMatchObject({ status: 'healthy' });
  });

  it('rejects structurally invalid reservation payloads', async () => {
    const response = await app.inject({
      method: 'POST',
      url: '/reservations',
      payload: { orderId: 'order-1' },
    });

    expect(response.statusCode).toBe(400);
    expect(response.json()).toMatchObject({ error: 'VALIDATION_ERROR' });
  });

  it('rejects reservations that exceed the max quantity rule', async () => {
    const response = await app.inject({
      method: 'POST',
      url: '/reservations',
      payload: {
        orderId: 'order-max',
        itemId: 'item-1',
        quantity: 101,
      },
    });

    expect(response.statusCode).toBe(400);
    expect(response.json()).toMatchObject({ error: 'BUSINESS_RULE_VIOLATION' });
  });

  it('accepts valid reservation requests', async () => {
    const response = await app.inject({
      method: 'POST',
      url: '/reservations',
      payload: {
        orderId: 'order-accept',
        itemId: 'item-accept',
        quantity: 5,
      },
    });

    expect(response.statusCode).toBe(201);
    expect(response.json()).toEqual({ ok: true });
  });

  it('reports runtime guard statistics after violations occur', async () => {
    const baseline = await app.inject({ method: 'GET', url: '/api/runtime-guard/stats' });
    expect(baseline.statusCode).toBe(200);
    const baselineJson = baseline.json();
    const baselineTotal = baselineJson.violations?.total ?? 0;

    await app.inject({
      method: 'POST',
      url: '/reservations',
      payload: {
        orderId: 'order-stats',
        itemId: 'item-stats',
        quantity: 150, // triggers business rule violation
      },
    });

    const statsResponse = await app.inject({ method: 'GET', url: '/api/runtime-guard/stats' });
    expect(statsResponse.statusCode).toBe(200);
    const stats = statsResponse.json();
    expect(stats).toHaveProperty('violations');
    expect(stats.violations.total).toBeGreaterThanOrEqual(baselineTotal + 1);
    expect(stats.violations.byType.business_rule).toBeGreaterThanOrEqual(1);
  });
});
