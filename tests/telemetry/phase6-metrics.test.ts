import { beforeEach, describe, expect, it, vi } from 'vitest';

const otelMocks = vi.hoisted(() => {
  const startSpan = vi.fn();
  const createCounter = vi.fn(() => ({ add: vi.fn() }));
  const createHistogram = vi.fn(() => ({ record: vi.fn() }));
  const createObservableGauge = vi.fn(() => ({ name: 'gauge' }));
  const addBatchObservableCallback = vi.fn();
  return {
    startSpan,
    createCounter,
    createHistogram,
    createObservableGauge,
    addBatchObservableCallback,
  };
});

vi.mock('@opentelemetry/api', () => ({
  metrics: {
    getMeter: () => ({
      createCounter: otelMocks.createCounter,
      createHistogram: otelMocks.createHistogram,
      createObservableGauge: otelMocks.createObservableGauge,
      addBatchObservableCallback: otelMocks.addBatchObservableCallback,
    }),
  },
  trace: {
    getTracer: () => ({
      startSpan: otelMocks.startSpan,
    }),
  },
  SpanStatusCode: {
    OK: 1,
    ERROR: 2,
  },
}));

import { Phase6Telemetry } from '../../src/telemetry/phase6-metrics.js';

describe('Phase6Telemetry metadata sanitization', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    otelMocks.startSpan.mockReturnValue({
      setAttributes: vi.fn(),
      setStatus: vi.fn(),
      end: vi.fn(),
    });
  });

  it('drops unsupported metadata values before span creation', async () => {
    await expect(
      Phase6Telemetry.instrumentScaffoldOperation('sanitize', async () => 'ok', {
        primitiveString: 'value',
        primitiveNumber: 42,
        primitiveBoolean: true,
        objectValue: { nested: true },
        arrayValue: [1, 2, 3],
        nullValue: null,
        undefinedValue: undefined,
      })
    ).resolves.toBe('ok');

    expect(otelMocks.startSpan).toHaveBeenCalledTimes(1);
    const [, spanOptions] = otelMocks.startSpan.mock.calls[0] as [
      string,
      { attributes: Record<string, unknown> },
    ];

    expect(spanOptions.attributes).toMatchObject({
      'phase6.operation': 'scaffold',
      'phase6.operation_name': 'sanitize',
      primitiveString: 'value',
      primitiveNumber: 42,
      primitiveBoolean: true,
    });
    expect(spanOptions.attributes).not.toHaveProperty('objectValue');
    expect(spanOptions.attributes).not.toHaveProperty('arrayValue');
    expect(spanOptions.attributes).not.toHaveProperty('nullValue');
    expect(spanOptions.attributes).not.toHaveProperty('undefinedValue');
  });
});
