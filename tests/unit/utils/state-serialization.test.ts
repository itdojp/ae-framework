import { describe, expect, it } from 'vitest';

import { encodeSpecialValue, reviveSpecialValue } from '../../../src/utils/state-serialization.js';

describe('state-serialization helpers', () => {
  it('encodes and revives typed arrays', () => {
    const original = new Uint16Array([1, 2, 65535]);
    const encoded = encodeSpecialValue(original);
    const revived = reviveSpecialValue(encoded);

    expect(encoded).toEqual({
      __ae_type: 'TypedArray',
      name: 'Uint16Array',
      values: [1, 2, 65535],
    });
    expect(revived).toBeInstanceOf(Uint16Array);
    expect(Array.from(revived as Uint16Array)).toEqual([1, 2, 65535]);
  });

  it('encodes and revives DataView values', () => {
    const buffer = new ArrayBuffer(4);
    const view = new DataView(buffer);
    view.setInt16(0, 42);
    view.setInt16(2, -7);

    const revived = reviveSpecialValue(encodeSpecialValue(view));

    expect(revived).toBeInstanceOf(DataView);
    const revivedView = revived as DataView;
    expect(revivedView.getInt16(0)).toBe(42);
    expect(revivedView.getInt16(2)).toBe(-7);
  });

  it('recursively revives nested serialized values', () => {
    const payload = {
      arr: encodeSpecialValue(new Int8Array([5, -5])),
      nested: {
        buf: encodeSpecialValue(Uint8Array.from([9, 8, 7]).buffer),
      },
    };

    const revived = reviveSpecialValue(payload) as {
      arr: Int8Array;
      nested: { buf: ArrayBuffer };
    };

    expect(revived.arr).toBeInstanceOf(Int8Array);
    expect(Array.from(revived.arr)).toEqual([5, -5]);
    expect(revived.nested.buf).toBeInstanceOf(ArrayBuffer);
    expect(Array.from(new Uint8Array(revived.nested.buf))).toEqual([9, 8, 7]);
  });
});
