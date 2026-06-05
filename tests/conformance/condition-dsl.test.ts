import { readFileSync } from 'node:fs';
import { describe, expect, it } from 'vitest';

import {
  createConditionValidators,
  evaluateConformanceConditionExpression,
} from '../../src/conformance/condition-dsl.js';
import { createEncryptedChatDefaultRules } from '../../src/conformance/default-rules.js';

const validators = {
  ...createConditionValidators(),
  isString: (value: unknown) => typeof value === 'string',
  isNumber: (value: unknown) => typeof value === 'number' && !Number.isNaN(value),
  isBoolean: (value: unknown) => typeof value === 'boolean',
};

const utils = {
  hash: (value: unknown) => String(value).length,
};

const baseData = {
  message: {
    encryption: 'AES-256-GCM',
    authTag: 'MTIzNDU2Nzg5MDEyMzQ1Ng==',
  },
  metrics: {
    oneTimePreKeyCount: 128,
    activeDeviceCount: 1,
    deliveryLatencyMs: 200,
    gdprRetentionDays: 180,
    invalidAuthTagLogged: true,
  },
  session: {
    state: 'active',
    devicesActive: true,
    chainKeys: ['chain-key'],
    messagesSinceRotation: 10,
    hoursSinceRotation: 1,
  },
  audit: {
    appendOnly: true,
    payloadAligned: true,
  },
};

const evaluate = (expression: string, data: unknown = baseData): unknown =>
  evaluateConformanceConditionExpression(expression, {
    data,
    context: { environment: 'test' },
    validators,
    utils,
  });

describe('conformance condition DSL', () => {
  it('evaluates repository default rule expressions without executable JavaScript evaluation', () => {
    for (const rule of createEncryptedChatDefaultRules('2026-06-05T00:00:00.000Z')) {
      expect(evaluate(rule.condition.expression), rule.name).toBe(true);
    }
  });

  it('evaluates optional paths, nullish defaults, comparisons, and helper calls', () => {
    expect(evaluate('Number(data.metrics?.missingCount ?? 0) >= 0')).toBe(true);
    expect(evaluate('Boolean(data.audit?.appendOnly) && validators.isBase64Like(data.message.authTag)')).toBe(true);
    expect(evaluate('data.message?.encryption !== "plaintext"')).toBe(true);
  });

  it('keeps symbolic legacy monitor expressions permissive', () => {
    expect(evaluate('required && string')).toBe(true);
    expect(evaluate('method status headers request_schema response_schema timeout')).toBe(true);
  });

  it('returns false for missing data paths instead of treating them as symbolic expressions', () => {
    expect(evaluate('data.missing')).toBeUndefined();
    expect(Boolean(evaluate('data.missing'))).toBe(false);
  });

  it('rejects code execution syntax and ambient authority identifiers', () => {
    const expressions = [
      'process.env.SECRET',
      'globalThis.fetch',
      'require("node:fs")',
      'data.constructor.constructor("return process")()',
      'import("node:fs")',
      'data.value; process.exit(1)',
      '`template`',
      '/.*/.test(data.message.authTag)',
    ];

    for (const expression of expressions) {
      expect(() => evaluate(expression), expression).toThrow();
    }
  });

  it('rejects loose equality rather than silently changing JavaScript coercion semantics', () => {
    expect(() => evaluate('data.metrics.activeDeviceCount == "1"')).toThrow(/loose equality/i);
    expect(() => evaluate('data.metrics.activeDeviceCount != "0"')).toThrow(/loose equality/i);
    expect(evaluate('data.metrics.activeDeviceCount === 1')).toBe(true);
    expect(evaluate('data.metrics.activeDeviceCount !== 0')).toBe(true);
  });

  it('rejects unknown roots and unsupported call shapes during syntax validation', () => {
    expect(() => evaluate('dat.message.authTag')).toThrow(/unknown identifier/i);
    expect(() => evaluate('foo()')).toThrow(/unsupported function call/i);
    expect(() => evaluate('data.message.authTag()')).toThrow(/approved helper calls/i);
  });

  it('does not use dynamic code evaluation primitives in conformance rule evaluation sources', () => {
    const files = [
      'src/conformance/rule-engine.ts',
      'src/conformance/condition-dsl.ts',
    ];
    const forbidden = [
      /\bnew\s+Function\b/,
      /\beval\s*\(/,
      /\bimport\s*\(/,
    ];

    for (const file of files) {
      const source = readFileSync(file, 'utf8');
      for (const pattern of forbidden) {
        expect(source, `${file} must not match ${pattern}`).not.toMatch(pattern);
      }
    }
  });
});
