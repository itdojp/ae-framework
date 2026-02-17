import { describe, expect, it } from 'vitest';

import { encodeSpecialValue } from '../../../src/utils/state-serialization.js';
import { reviveStateEntryData } from '../../../src/utils/state-entry-revival.js';

describe('state-entry-revival helper', () => {
  it('returns Buffer as-is for compressed entries', () => {
    const rawBuffer = Buffer.from('compressed');
    const revived = reviveStateEntryData({ compressed: true, data: rawBuffer });

    expect(Buffer.isBuffer(revived)).toBe(true);
    expect((revived as Buffer).equals(rawBuffer)).toBe(true);
  });

  it('revives Buffer JSON representation and numeric arrays', () => {
    const fromJson = reviveStateEntryData({
      compressed: true,
      data: { type: 'Buffer', data: [65, 66, 67] },
    });
    const fromNumbers = reviveStateEntryData({
      compressed: true,
      data: [68, 69, 70],
    });

    expect((fromJson as Buffer).toString('utf8')).toBe('ABC');
    expect((fromNumbers as Buffer).toString('utf8')).toBe('DEF');
  });

  it('revives encoded typed arrays and non-compressed payloads', () => {
    const encodedTyped = encodeSpecialValue(new Uint8Array([1, 2, 3]));
    const revivedTyped = reviveStateEntryData({ compressed: true, data: encodedTyped });

    expect(Buffer.isBuffer(revivedTyped)).toBe(true);
    expect(Array.from(revivedTyped as Buffer)).toEqual([1, 2, 3]);

    const plain = reviveStateEntryData({ compressed: false, data: { ok: true, nested: [1, 2, 3] } });
    expect(plain).toEqual({ ok: true, nested: [1, 2, 3] });
  });
});
