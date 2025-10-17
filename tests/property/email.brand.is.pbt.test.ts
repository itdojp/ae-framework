import { afterEach, beforeAll, describe, expect, it, vi } from 'vitest';
import fc from 'fast-check';
import { Email, makeEmail } from '../../src/lib/email';

beforeAll(() => {
  const isCI = process.env.CI === '1';
  fc.configureGlobal({
    numRuns: isCI ? 50 : 100,
    interruptAfterTimeLimit: isCI ? 5000 : undefined,
    endOnFailure: true,
  });
});

afterEach(() => {
  try {
    vi.useRealTimers();
  } catch (error) {
    // ignore if timers were not mocked
  }
});

function normalizeDotsAndSymbols(value: string): string {
  return value
    .replace(/\.+/g, '.')
    .replace(/[._+-]{2,}/g, (segment) => segment[0]);
}

function normalizeLocalPart(head: string, tail: string): string {
  const cleanedTail = normalizeDotsAndSymbols(
    tail
      .replace(/[^a-zA-Z0-9._+-]/g, '')
      .replace(/[._+-]+$/g, ''),
  );

  const remainder = cleanedTail.length > 0 ? cleanedTail : '0';

  return normalizeDotsAndSymbols(`${head}${remainder}`).replace(/\.$/, '');
}

describe('PBT: Email brand is() and make()', () => {
  it('is() returns true for values produced by make()', async () => {
    const headChars = 'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789';
    const tailChars = headChars + '._+-';
    const arbLocal = fc.tuple(
      fc.constantFrom(...headChars.split('')),
      fc.stringOf(fc.constantFrom(...tailChars.split('')), { maxLength: 9 })
    ).map(([head, tail]) => normalizeLocalPart(head, tail));
    await fc.assert(fc.asyncProperty(
      arbLocal,
      async (local) => {
        const raw = `${local}@Example.COM`;
        const e = makeEmail(raw);
        expect(Email.is(e)).toBe(true);
      }
    ), { numRuns: 30 });
  });
});
