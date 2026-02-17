import { reviveSpecialValue } from './state-serialization.js';

export interface CompressedStateEntryLike {
  compressed?: boolean;
  data?: unknown;
}

export function reviveStateEntryData(rawEntry: CompressedStateEntryLike): unknown {
  if (rawEntry.compressed) {
    // `compressed` entries are expected to carry byte payloads (Buffer/Uint8Array/etc).
    // Accept multiple representations to support persisted/imported state shapes.
    const rawData = rawEntry.data as any;
    // Only revive marker objects (e.g. {__ae_type: string}); do not traverse real TypedArray instances,
    // otherwise they get converted into plain objects and become unusable as byte payloads.
    const data =
      rawData && typeof rawData === 'object' && typeof (rawData as any).__ae_type === 'string'
        ? (reviveSpecialValue(rawData) as any)
        : rawData;

    if (Buffer.isBuffer(data)) {
      return data;
    }

    if (data && typeof data === 'object') {
      // TypedArray / DataView
      if (ArrayBuffer.isView(data)) {
        const view = data as ArrayBufferView;
        return Buffer.from(new Uint8Array(view.buffer, view.byteOffset, view.byteLength));
      }
      // ArrayBuffer
      if (typeof ArrayBuffer !== 'undefined' && data instanceof ArrayBuffer) {
        return Buffer.from(new Uint8Array(data));
      }
      // SharedArrayBuffer (when available)
      if (typeof SharedArrayBuffer !== 'undefined' && data instanceof SharedArrayBuffer) {
        return Buffer.from(new Uint8Array(data));
      }
      // Buffer JSON form (e.g. {"type":"Buffer","data":[...]})
      if (data.type === 'Buffer' && Array.isArray(data.data)) {
        return Buffer.from(data.data);
      }
      // Legacy number[] form
      if (Array.isArray(data)) {
        let allNumbers = true;
        const buffer = Buffer.alloc(data.length);
        for (let i = 0; i < data.length; i++) {
          const value = (data as any)[i];
          if (typeof value !== 'number') {
            allNumbers = false;
            break;
          }
          buffer[i] = value;
        }
        if (allNumbers) {
          return buffer;
        }
      }
    }

    // Keep legacy behavior: if we can't map the payload into a byte representation, preserve it as-is.
    // Note: downstream decompression may fail if callers attempt to treat it as bytes.
    return data;
  }
  return reviveSpecialValue(rawEntry.data);
}
