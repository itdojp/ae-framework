/**
 * Security Headers Test Suite
 * Tests the security headers middleware implementation
 */

import { describe, it, expect, beforeAll, afterAll } from 'vitest';
import { createServer } from '../../src/api/server.js';
import { FastifyInstance } from 'fastify';

describe('Security Headers Middleware', () => {
  let app: FastifyInstance;

  beforeAll(async () => {
    app = await createServer();
    await app.ready();
  });

  afterAll(async () => {
    await app.close();
  });

  it('should add Content-Security-Policy header', async () => {
    const response = await app.inject({
      method: 'GET',
      url: '/health'
    });

    expect(response.statusCode).toBe(200);
    expect(response.headers['content-security-policy']).toBeDefined();
    expect(response.headers['content-security-policy']).toContain("default-src 'self'");
  });

  it('should add X-Frame-Options header', async () => {
    const response = await app.inject({
      method: 'GET',
      url: '/health'
    });

    expect(response.headers['x-frame-options']).toBe('DENY');
  });

  it('should add X-Content-Type-Options header', async () => {
    const response = await app.inject({
      method: 'GET',
      url: '/health'
    });

    expect(response.headers['x-content-type-options']).toBe('nosniff');
  });

  it('should add Referrer-Policy header', async () => {
    const response = await app.inject({
      method: 'GET',
      url: '/health'
    });

    expect(response.headers['referrer-policy']).toBe('strict-origin-when-cross-origin');
  });

  it('should add X-XSS-Protection header', async () => {
    const response = await app.inject({
      method: 'GET',
      url: '/health'
    });

    expect(response.headers['x-xss-protection']).toBe('1; mode=block');
  });

  it('should add Permissions-Policy header', async () => {
    const response = await app.inject({
      method: 'GET',
      url: '/health'
    });

    expect(response.headers['permissions-policy']).toBeDefined();
    expect(response.headers['permissions-policy']).toContain('camera=()');
  });

  it('should remove server identification headers', async () => {
    const response = await app.inject({
      method: 'GET',
      url: '/health'
    });

    expect(response.headers['x-powered-by']).toBeUndefined();
    expect(response.headers['server']).toBeUndefined();
  });

  it('should NOT add HSTS header for HTTP requests', async () => {
    const response = await app.inject({
      method: 'GET',
      url: '/health'
    });

    // HSTS should not be present for HTTP requests
    expect(response.headers['strict-transport-security']).toBeUndefined();
  });

  it('should work with POST requests', async () => {
    const response = await app.inject({
      method: 'POST',
      url: '/reservations',
      payload: {
        orderId: 'test-order',
        itemId: 'test-item',
        quantity: 1
      }
    });

    expect(response.headers['content-security-policy']).toBeDefined();
    expect(response.headers['x-frame-options']).toBe('DENY');
    expect(response.headers['x-content-type-options']).toBe('nosniff');
  });

  it('should handle health check endpoint correctly', async () => {
    const response = await app.inject({
      method: 'GET',
      url: '/health'
    });

    expect(response.statusCode).toBe(200);
    
    const body = JSON.parse(response.body);
    expect(body.status).toBe('healthy');
    expect(body.service).toBe('ae-framework-api');
    expect(body.timestamp).toBeDefined();
    
    // Verify all security headers are present
    expect(response.headers['content-security-policy']).toBeDefined();
    expect(response.headers['x-frame-options']).toBeDefined();
    expect(response.headers['x-content-type-options']).toBeDefined();
    expect(response.headers['referrer-policy']).toBeDefined();
    expect(response.headers['permissions-policy']).toBeDefined();
  });
});