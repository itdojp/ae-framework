const TYPED_ARRAY_CTORS: Record<string, { from(values: Iterable<any>): ArrayBufferView }> = {
  Int8Array,
  Uint8Array,
  Uint8ClampedArray,
  Int16Array,
  Uint16Array,
  Int32Array,
  Uint32Array,
  Float32Array,
  Float64Array,
  BigInt64Array,
  BigUint64Array,
};

type EncodedSpecial =
  | { __ae_type: 'TypedArray'; name: string; values: Array<any> }
  | { __ae_type: 'DataView'; bytes: number[] }
  | { __ae_type: 'ArrayBuffer'; bytes: number[] }
  | { __ae_type: 'SharedArrayBuffer'; bytes: number[] };

export function encodeSpecialValue(value: unknown): unknown {
  if (value && typeof Buffer !== 'undefined' && Buffer.isBuffer(value)) {
    return value;
  }
  if (value && ArrayBuffer.isView(value)) {
    if (value instanceof DataView) {
      const bytes = Array.from(new Uint8Array(value.buffer, value.byteOffset, value.byteLength));
      return { __ae_type: 'DataView', bytes } satisfies EncodedSpecial;
    }
    const name = value.constructor?.name;
    if (name && TYPED_ARRAY_CTORS[name]) {
      const values = Array.from(value as any);
      return { __ae_type: 'TypedArray', name, values } satisfies EncodedSpecial;
    }
  }
  if (typeof ArrayBuffer !== 'undefined' && value instanceof ArrayBuffer) {
    return {
      __ae_type: 'ArrayBuffer',
      bytes: Array.from(new Uint8Array(value)),
    } satisfies EncodedSpecial;
  }
  if (typeof SharedArrayBuffer !== 'undefined' && value instanceof SharedArrayBuffer) {
    return {
      __ae_type: 'SharedArrayBuffer',
      bytes: Array.from(new Uint8Array(value)),
    } satisfies EncodedSpecial;
  }
  return value;
}

export function reviveSpecialValue(value: unknown, seen = new WeakSet<object>()): unknown {
  if (!value || typeof value !== 'object') {
    return value;
  }

  const marker = (value as { __ae_type?: string }).__ae_type;
  if (marker === 'TypedArray') {
    const { name, values } = value as EncodedSpecial & { name: string; values: Array<any> };
    const ctor = TYPED_ARRAY_CTORS[name];
    if (ctor) {
      return ctor.from(values);
    }
    return values;
  }
  if (marker === 'DataView') {
    const bytes = (value as EncodedSpecial & { bytes: number[] }).bytes ?? [];
    const buffer = new ArrayBuffer(bytes.length);
    new Uint8Array(buffer).set(bytes);
    return new DataView(buffer);
  }
  if (marker === 'ArrayBuffer') {
    const bytes = (value as EncodedSpecial & { bytes: number[] }).bytes ?? [];
    const buffer = new ArrayBuffer(bytes.length);
    new Uint8Array(buffer).set(bytes);
    return buffer;
  }
  if (marker === 'SharedArrayBuffer') {
    const bytes = (value as EncodedSpecial & { bytes: number[] }).bytes ?? [];
    if (typeof SharedArrayBuffer !== 'undefined') {
      const shared = new SharedArrayBuffer(bytes.length);
      new Uint8Array(shared).set(bytes);
      return shared;
    }
    const buffer = new ArrayBuffer(bytes.length);
    new Uint8Array(buffer).set(bytes);
    return buffer;
  }

  if (seen.has(value as object)) {
    return value;
  }
  seen.add(value as object);

  if (Array.isArray(value)) {
    return value.map((item) => reviveSpecialValue(item, seen));
  }

  const result: Record<string, unknown> = {};
  for (const [key, val] of Object.entries(value)) {
    result[key] = reviveSpecialValue(val, seen);
  }
  return result;
}
