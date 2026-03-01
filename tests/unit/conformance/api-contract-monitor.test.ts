import { describe, expect, it } from 'vitest';
import type { ConformanceRule, RuntimeContext } from '../../../src/conformance/types.js';
import { APIContractMonitor } from '../../../src/conformance/monitors/api-contract-monitor.js';

const now = '2026-03-02T00:00:00.000Z';

const context: RuntimeContext = {
  timestamp: now,
  executionId: 'f7541d8d-9f4a-4f47-a3ac-13f3e749e1bc',
  environment: 'test',
  metadata: {}
};

const rule: ConformanceRule = {
  id: '767a5720-63f2-46f9-a2f3-8407f786f0d8',
  name: 'API status contract',
  description: 'Validate method/status pair.',
  category: 'api_contract',
  severity: 'major',
  enabled: true,
  condition: {
    expression: 'method status',
    variables: [],
    constraints: {}
  },
  actions: ['log_violation'],
  metadata: {
    createdAt: now,
    updatedAt: now,
    version: '1.0.0',
    tags: ['test']
  }
};

function createMonitor(): APIContractMonitor {
  const monitor = new APIContractMonitor();
  monitor.addContractSpec('/v1/messages', {
    method: 'POST',
    path: '/v1/messages',
    statusCodes: [202]
  });
  return monitor;
}

describe('APIContractMonitor metrics wiring', () => {
  it('derives network/db metrics from response headers', async () => {
    const monitor = createMonitor();
    await monitor.updateRule(rule);

    const result = await monitor.verify(
      {
        method: 'POST',
        url: 'https://example.local/v1/messages',
        path: '/v1/messages',
        headers: {
          'content-type': 'application/json'
        },
        response: {
          status: 202,
          headers: {
            'X-Network-Calls': '3',
            'X-DB-Query-Count': '5'
          },
          time: 42
        },
        timestamp: now
      },
      context
    );

    expect(result.status).toBe('pass');
    expect(result.metrics.networkCalls).toBe(3);
    expect(result.metrics.dbQueries).toBe(5);
  });

  it('falls back to context metadata for dbQueries when headers are missing', async () => {
    const monitor = createMonitor();
    await monitor.updateRule(rule);

    const result = await monitor.verify(
      {
        method: 'POST',
        url: 'https://example.local/v1/messages',
        path: '/v1/messages',
        headers: {},
        response: {
          status: 202,
          headers: {},
          time: 35
        },
        timestamp: now
      },
      {
        ...context,
        metadata: {
          dbQueries: 4
        }
      }
    );

    expect(result.status).toBe('pass');
    expect(result.metrics.networkCalls).toBe(1);
    expect(result.metrics.dbQueries).toBe(4);
  });

  it('ignores malformed string counters and falls back to defaults', async () => {
    const monitor = createMonitor();
    await monitor.updateRule(rule);

    const result = await monitor.verify(
      {
        method: 'POST',
        url: 'https://example.local/v1/messages',
        path: '/v1/messages',
        headers: {},
        response: {
          status: 202,
          headers: {
            'x-network-calls': '1.5',
            'x-db-query-count': '12ms'
          },
          time: 20
        },
        timestamp: now
      },
      context
    );

    expect(result.status).toBe('pass');
    expect(result.metrics.networkCalls).toBe(1);
    expect(result.metrics.dbQueries).toBe(0);
  });

  it('keeps metrics zero for invalid input payload', async () => {
    const monitor = createMonitor();
    await monitor.updateRule(rule);

    const result = await monitor.verify(
      {
        invalid: true
      },
      context
    );

    expect(result.status).toBe('skip');
    expect(result.ruleId).toBe('invalid-data');
    expect(result.metrics.networkCalls).toBe(0);
    expect(result.metrics.dbQueries).toBe(0);
  });
});
