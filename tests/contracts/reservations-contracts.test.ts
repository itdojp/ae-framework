import { describe, it, expect } from 'vitest';
import { readFileSync, readdirSync, existsSync } from 'node:fs';
import { join, basename } from 'node:path';
import { z } from 'zod';
import { CommonSchemas } from '../../src/telemetry/runtime-guards.js';

const CONTRACTS_DIR = join(process.cwd(), 'contracts');

const ContractSchema = z.object({
  id: z.string().min(1),
  description: z.string().min(1),
  request: z.object({
    method: z.enum(['POST', 'DELETE']),
    path: z.string().min(1),
    body: z.unknown().optional()
  }),
  response: z.object({
    status: z.number().int().positive(),
    body: z.unknown().nullable()
  })
});

type Contract = z.infer<typeof ContractSchema>;

function loadContracts(): Contract[] {
  if (!existsSync(CONTRACTS_DIR)) {
    return [];
  }

  const allowList = (process.env.PACT_CONTRACTS ?? '')
    .split(',')
    .map((item) => item.trim())
    .filter(Boolean);

  const files = readdirSync(CONTRACTS_DIR).filter((file) => file.endsWith('.json'));
  const selected = allowList.length === 0
    ? files
    : files.filter((file) => allowList.includes(file) || allowList.includes(basename(file, '.json')));

  return selected.map((file) => {
    const raw = readFileSync(join(CONTRACTS_DIR, file), 'utf8');
    return ContractSchema.parse(JSON.parse(raw));
  });
}

const reservationRequestSchema = CommonSchemas.ReservationRequest;
const reservationResponseSchema = CommonSchemas.ReservationResponse;

describe('Reservations provider contracts', () => {
  const contracts = loadContracts();

  if (contracts.length === 0) {
    it.skip('No reservation contracts discovered', () => {});
    return;
  }

  for (const contract of contracts) {
    it(`validates contract: ${contract.id}`, () => {
      if (contract.request.method === 'POST' && contract.request.path === '/reservations') {
        expect(reservationRequestSchema.parse(contract.request.body)).toBeDefined();
        const response = reservationResponseSchema.parse(contract.response.body ?? {});
        expect(typeof response.ok).toBe('boolean');
      } else if (contract.request.method === 'DELETE' && contract.request.path.startsWith('/reservations/')) {
        expect(contract.response.status).toBe(204);
        expect(contract.response.body).toBeNull();
      } else {
        throw new Error(`Unsupported contract configuration: ${contract.id}`);
      }
    });
  }
});
