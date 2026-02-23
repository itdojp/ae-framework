import { reviveSpecialValue } from './state-serialization.js';

export interface CompressedStateEntryLike {
  compressed?: boolean;
  data?: unknown;
}

export function reviveStateEntryData(rawEntry: CompressedStateEntryLike): unknown {
  if (rawEntry.compressed) {
    // `compressed` entries are expected to carry byte payloads (Buffer/Uint8Array/etc).
    // Accept multiple representations to support persisted/imported state shapes.
    const rawData = rawEntry.data;
    // Only revive marker objects (e.g. {__ae_type: string}); do not traverse real TypedArray instances,
    // otherwise they get converted into plain objects and become unusable as byte payloads.
    const data =
      rawData &&
      typeof rawData === 'object' &&
      typeof (rawData as { __ae_type?: unknown }).__ae_type === 'string'
        ? reviveSpecialValue(rawData)
        : rawData;

    if (Buffer.isBuffer(data)) {
      return data;
    }

    if (data && typeof data === 'object') {
      const dataRecord = data as Record<string, unknown>;
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
      if (dataRecord['type'] === 'Buffer' && Array.isArray(dataRecord['data'])) {
        return Buffer.from(dataRecord['data']);
      }
      // Legacy number[] form
      if (Array.isArray(data)) {
        let allNumbers = true;
        const buffer = Buffer.alloc(data.length);
        for (let i = 0; i < data.length; i++) {
          const value = data[i];
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
