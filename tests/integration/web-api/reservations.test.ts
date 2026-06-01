import { describe, expect, it } from 'vitest';
import { buildApp, resolvePrincipalFromHeaders, seedRepo } from '../../../src/web-api/app';
import { InMemoryReservationRepository } from '../../../src/web-api/repository';
import {
  applyIntegrationRetry,
  registerIntegrationCleanup,
} from '../../_helpers/integration-test-utils.js';
import '../setup';

// test:integration:webapi で実行

applyIntegrationRetry(it);

async function buildTestApp() {
  const repo = new InMemoryReservationRepository();
  const app = buildApp(repo, { resolvePrincipal: resolvePrincipalFromHeaders });
  await app.ready();
  registerIntegrationCleanup(async () => {
    try {
      await app.close();
    } catch (error) {
      console.warn('Reservation API cleanup failed:', error);
    }
  });
  return { repo, app };
}

const principalHeaders = (userId: string) => ({ 'x-user-id': userId });

describe('web api / reservations', () => {
  it('fails closed when no authenticated principal resolver is configured', async () => {
    const repo = new InMemoryReservationRepository();
    const app = buildApp(repo);
    await app.ready();
    registerIntegrationCleanup(async () => {
      await app.close();
    });
    seedRepo(repo, { 'item-1': 5 });

    const res = await app.inject({
      method: 'POST',
      url: '/reservations',
      headers: principalHeaders('u1'),
      payload: { sku: 'item-1', quantity: 1, requestId: 'default-fail-closed', userId: 'u1' },
    });

    expect(res.statusCode).toBe(401);
    expect(res.json()).toMatchObject({ error: 'unauthorized' });
    expect(repo.getStock('item-1')).toBe(5);
  });

  it('creates a reservation when stock is sufficient for the authenticated principal', async () => {
    const { repo, app } = await buildTestApp();
    seedRepo(repo, { 'item-1': 5 });
    const res = await app.inject({
      method: 'POST',
      url: '/reservations',
      headers: principalHeaders('u1'),
      payload: { sku: 'item-1', quantity: 1, requestId: 'r1', userId: 'u1' },
    });
    expect(res.statusCode).toBe(200);
    expect(repo.getStock('item-1')).toBe(4);
  });

  it('is idempotent for the same principal, requestId, and payload', async () => {
    const { repo, app } = await buildTestApp();
    seedRepo(repo, { 'item-1': 5 });
    const payload = { sku: 'item-1', quantity: 1, requestId: 'r2', userId: 'u1' };
    const first = await app.inject({
      method: 'POST',
      url: '/reservations',
      headers: principalHeaders('u1'),
      payload,
    });
    const second = await app.inject({
      method: 'POST',
      url: '/reservations',
      headers: principalHeaders('u1'),
      payload,
    });
    expect(first.statusCode).toBe(200);
    expect(second.statusCode).toBe(200);
    expect(first.json()).toEqual(second.json());
    expect(repo.getStock('item-1')).toBe(4);
  });

  it('returns 409 when stock is insufficient and caches same-principal rejection', async () => {
    const { repo, app } = await buildTestApp();
    seedRepo(repo, { 'item-1': 1 });
    const payload = { sku: 'item-1', quantity: 10, requestId: 'r3', userId: 'u1' };
    const first = await app.inject({
      method: 'POST',
      url: '/reservations',
      headers: principalHeaders('u1'),
      payload,
    });
    const second = await app.inject({
      method: 'POST',
      url: '/reservations',
      headers: principalHeaders('u1'),
      payload,
    });
    expect(first.statusCode).toBe(409);
    expect(second.statusCode).toBe(409);
    expect(first.json()).toEqual(second.json());
    expect(repo.getStock('item-1')).toBe(1);
  });

  it('returns 409 without leaking a record when a duplicate key crosses principals', async () => {
    const { repo, app } = await buildTestApp();
    seedRepo(repo, { 'item-1': 5 });
    const first = await app.inject({
      method: 'POST',
      url: '/reservations',
      headers: principalHeaders('u1'),
      payload: { sku: 'item-1', quantity: 1, requestId: 'shared-key', userId: 'u1' },
    });
    const second = await app.inject({
      method: 'POST',
      url: '/reservations',
      headers: principalHeaders('u2'),
      payload: { sku: 'item-1', quantity: 1, requestId: 'shared-key', userId: 'u2' },
    });

    expect(first.statusCode).toBe(200);
    expect(second.statusCode).toBe(409);
    expect(second.json()).toMatchObject({ error: 'idempotency_conflict', reason: 'principal_mismatch' });
    expect(second.json()).not.toHaveProperty('record');
    expect(repo.getStock('item-1')).toBe(4);
  });

  it('returns 409 when the same principal reuses a key with a different quantity', async () => {
    const { repo, app } = await buildTestApp();
    seedRepo(repo, { 'item-1': 5 });
    const first = await app.inject({
      method: 'POST',
      url: '/reservations',
      headers: principalHeaders('u1'),
      payload: { sku: 'item-1', quantity: 1, requestId: 'payload-key', userId: 'u1' },
    });
    const second = await app.inject({
      method: 'POST',
      url: '/reservations',
      headers: principalHeaders('u1'),
      payload: { sku: 'item-1', quantity: 2, requestId: 'payload-key', userId: 'u1' },
    });

    expect(first.statusCode).toBe(200);
    expect(second.statusCode).toBe(409);
    expect(second.json()).toMatchObject({ error: 'idempotency_conflict', reason: 'payload_mismatch' });
    expect(second.json()).not.toHaveProperty('record');
    expect(repo.getStock('item-1')).toBe(4);
  });

  it('returns 409 when the same principal reuses a key with a different SKU', async () => {
    const { repo, app } = await buildTestApp();
    seedRepo(repo, { 'item-1': 5, 'item-2': 5 });
    const first = await app.inject({
      method: 'POST',
      url: '/reservations',
      headers: principalHeaders('u1'),
      payload: { sku: 'item-1', quantity: 1, requestId: 'sku-key', userId: 'u1' },
    });
    const second = await app.inject({
      method: 'POST',
      url: '/reservations',
      headers: principalHeaders('u1'),
      payload: { sku: 'item-2', quantity: 1, requestId: 'sku-key', userId: 'u1' },
    });

    expect(first.statusCode).toBe(200);
    expect(second.statusCode).toBe(409);
    expect(second.json()).toMatchObject({ error: 'idempotency_conflict', reason: 'payload_mismatch' });
    expect(second.json()).not.toHaveProperty('record');
    expect(repo.getStock('item-1')).toBe(4);
    expect(repo.getStock('item-2')).toBe(5);
  });

  it('rejects body userId that does not match the authenticated principal', async () => {
    const { repo, app } = await buildTestApp();
    seedRepo(repo, { 'item-1': 5 });
    const res = await app.inject({
      method: 'POST',
      url: '/reservations',
      headers: principalHeaders('u1'),
      payload: { sku: 'item-1', quantity: 1, requestId: 'mismatch', userId: 'u2' },
    });

    expect(res.statusCode).toBe(403);
    expect(res.json()).toMatchObject({ error: 'forbidden' });
    expect(repo.getStock('item-1')).toBe(5);
  });

  it('rejects unauthenticated multi-user requests instead of trusting body userId', async () => {
    const { repo, app } = await buildTestApp();
    seedRepo(repo, { 'item-1': 5 });
    const res = await app.inject({
      method: 'POST',
      url: '/reservations',
      payload: { sku: 'item-1', quantity: 1, requestId: 'unauthenticated', userId: 'u1' },
    });

    expect(res.statusCode).toBe(401);
    expect(res.json()).toMatchObject({ error: 'unauthorized' });
    expect(repo.getStock('item-1')).toBe(5);
  });

  it('rejects unauthenticated malformed requests before payload validation', async () => {
    const { repo, app } = await buildTestApp();
    seedRepo(repo, { 'item-1': 5 });
    const res = await app.inject({
      method: 'POST',
      url: '/reservations',
      payload: { sku: 'item-1', quantity: 1, userId: 'u1' },
    });

    expect(res.statusCode).toBe(401);
    expect(res.json()).toMatchObject({ error: 'unauthorized' });
    expect(repo.getStock('item-1')).toBe(5);
  });

  it('returns 400 when requestId is missing for an authenticated principal', async () => {
    const { repo, app } = await buildTestApp();
    seedRepo(repo, { 'item-1': 5 });
    const res = await app.inject({
      method: 'POST',
      url: '/reservations',
      headers: principalHeaders('u1'),
      payload: { sku: 'item-1', quantity: 1, userId: 'u1' },
    });
    expect(res.statusCode).toBe(400);
    expect(res.json()).toMatchObject({ error: 'invalid_request' });
  });
});
