import assert from 'node:assert/strict';
import Fastify from 'fastify';
import { z } from 'zod';
import { Before, After, Given, When, Then } from '@cucumber/cucumber';

const ReservationSchema = z.object({
  orderId: z.string().min(1),
  itemId: z.string().min(1),
  quantity: z.number().int().positive()
});

class ReservationWorld {
  constructor() {
    this.fastify = null;
    this.inventory = new Map();
    this.reservations = new Map();
    this.currentItemId = null;
    this.lastResponse = null;
  }

  async reset() {
    await this.dispose();
    this.inventory = new Map();
    this.reservations = new Map();
    this.currentItemId = null;
    this.lastResponse = null;

    this.fastify = Fastify({ logger: false });
    this.fastify.post('/reservations', async (request, reply) => {
      const parsed = ReservationSchema.safeParse(request.body);
      if (!parsed.success) {
        return reply.code(400).send({
          error: 'VALIDATION_ERROR',
          details: parsed.error.errors
        });
      }

      const { orderId, itemId, quantity } = parsed.data;
      const existing = this.reservations.get(orderId);
      if (existing) {
        return reply.code(201).send({
          orderId,
          itemId: existing.itemId,
          quantity: existing.quantity,
          status: 'confirmed'
        });
      }

      const record = this.inventory.get(itemId);
      if (!record || record.stock - record.reserved < quantity) {
        return reply.code(409).send({ error: 'INSUFFICIENT_STOCK' });
      }

      record.reserved += quantity;
      this.reservations.set(orderId, { itemId, quantity });

      return reply.code(201).send({
        orderId,
        itemId,
        quantity,
        status: 'confirmed'
      });
    });

    this.fastify.delete('/reservations/:orderId', async (request, reply) => {
      const { orderId } = request.params;
      const existing = this.reservations.get(orderId);
      if (!existing) {
        return reply.code(200).send({
          orderId,
          itemId: null,
          quantity: null,
          reservationId: null,
          status: 'not_found',
          cancelled: false,
          remaining: 0,
          ok: true,
        });
      }

      const record = this.inventory.get(existing.itemId);
      if (record) {
        record.reserved = Math.max(0, record.reserved - existing.quantity);
      }
      this.reservations.delete(orderId);

      return reply.code(200).send({
        orderId,
        itemId: existing.itemId,
        quantity: existing.quantity,
        reservationId: `reservation-${orderId}`,
        status: 'cancelled',
        cancelled: true,
        remaining: record ? record.stock - record.reserved : 0,
        ok: true,
      });
    });

    this.fastify.get('/items/:itemId/availability', async (request, reply) => {
      const { itemId } = request.params;
      const quantityValue = Number(request.query.quantity);
      if (!quantityValue || Number.isNaN(quantityValue)) {
        return reply.code(400).send({
          error: 'VALIDATION_ERROR',
          message: 'Quantity parameter is required and must be a number'
        });
      }
      const record = this.inventory.get(itemId);
      const available = record ? record.stock - record.reserved >= quantityValue : false;
      return reply.send({ itemId, quantity: quantityValue, available });
    });
  }

  async dispose() {
    if (this.fastify) {
      await this.fastify.close().catch(() => {});
      this.fastify = null;
    }
  }

  registerItem(itemId, units) {
    this.inventory.set(itemId, { stock: units, reserved: 0 });
    this.currentItemId = itemId;
  }

  registerExistingReservation(orderId, units) {
    if (!this.currentItemId) {
      throw new Error('No current item context available');
    }
    const record = this.inventory.get(this.currentItemId);
    if (!record) {
      throw new Error(`Item ${this.currentItemId} not found`);
    }
    record.reserved += units;
    this.reservations.set(orderId, { itemId: this.currentItemId, quantity: units });
  }

  async requestReservation(orderId, quantity) {
    assert.ok(this.fastify, 'Fastify instance is not initialised');
    if (!this.currentItemId) {
      throw new Error('No current item registered');
    }
    this.lastResponse = await this.fastify.inject({
      method: 'POST',
      url: '/reservations',
      payload: {
        orderId,
        itemId: this.currentItemId,
        quantity
      }
    });
  }

  async cancelReservation(orderId) {
    assert.ok(this.fastify, 'Fastify instance is not initialised');
    this.lastResponse = await this.fastify.inject({
      method: 'DELETE',
      url: `/reservations/${orderId}`
    });
  }

  getRemainingStock() {
    if (!this.currentItemId) {
      throw new Error('No current item registered');
    }
    const record = this.inventory.get(this.currentItemId);
    return record ? record.stock - record.reserved : 0;
  }
}

const world = new ReservationWorld();

Before(async () => {
  await world.reset();
});

After(async () => {
  await world.dispose();
});

Given('an item {string} with {int} units available', (itemId, units) => {
  world.registerItem(itemId, units);
});

Given('an item {string} with stock {int}', (itemId, units) => {
  world.registerItem(itemId, units);
});

Given('order {string} already reserved {int} units', (orderId, units) => {
  world.registerExistingReservation(orderId, units);
});

When('I request a reservation of {int} units for order {string}', async (units, orderId) => {
  await world.requestReservation(orderId, units);
});

When('I reserve {int} units for order {string}', async (units, orderId) => {
  await world.requestReservation(orderId, units);
});

When('I reserve {int} units again for order {string}', async (units, orderId) => {
  await world.requestReservation(orderId, units);
});

When('I cancel the reservation for order {string}', async (orderId) => {
  await world.cancelReservation(orderId);
});

Then('the reservation is rejected due to insufficient stock', () => {
  assert.ok(world.lastResponse, 'Reservation result is not recorded');
  assert.equal(world.lastResponse.statusCode, 409);
  const payload = world.lastResponse.json();
  assert.equal(payload.error, 'INSUFFICIENT_STOCK');
});

Then('the reservation is accepted and confirmed', () => {
  assert.ok(world.lastResponse, 'Reservation result is not recorded');
  assert.equal(world.lastResponse.statusCode, 201);
  const payload = world.lastResponse.json();
  assert.equal(payload.status, 'confirmed');
});

Then('the reservation cancellation is confirmed', () => {
  assert.ok(world.lastResponse, 'Reservation result is not recorded');
  assert.equal(world.lastResponse.statusCode, 200);
  const payload = world.lastResponse.json();
  assert.equal(payload.status, 'cancelled');
  assert.equal(payload.cancelled, true);
});

Then('the operation should be rejected with code {string}', (code) => {
  assert.ok(world.lastResponse, 'Reservation result is not recorded');
  assert.equal(String(world.lastResponse.statusCode), code === 'INSUFFICIENT_STOCK' ? '409' : code);
});

Then('the remaining stock should be {int}', (expectedStock) => {
  assert.equal(world.getRemainingStock(), expectedStock);
});
