import { describe, it, expect } from 'vitest';
import { EnhancedStateManager } from '../../src/utils/enhanced-state-manager.js';
import { createTempProjectRoot, cleanupProjectRoot } from '../_helpers/enhanced-state-manager.js';

const createManager = (root: string) =>
  new EnhancedStateManager(root, {
    // Force compression so that import path must revive byte payloads for decompression.
    compressionThreshold: 10,
    enableTransactions: false,
  });

const createCompressedExport = async () => {
  const srcRoot = await createTempProjectRoot('ae-1080-src-');
  const src = createManager(srcRoot);
  await src.initialize();

  const logicalKey = 'byte-import';
  const payload = {
    id: 'test-large-data',
    name: 'Large Test Data',
    type: 'test',
    version: '1.0.0',
    content: 'A'.repeat(100),
  };

  await src.saveSSOT(logicalKey, payload);
  const exported = await src.exportState();

  await src.shutdown();
  await cleanupProjectRoot(srcRoot);

  expect(exported.entries.length).toBe(1);
  expect(exported.entries[0].compressed).toBe(true);
  expect(Buffer.isBuffer(exported.entries[0].data)).toBe(true);

  return { exported, payload, logicalKey, compressed: exported.entries[0].data as Buffer };
};

describe('EnhancedStateManager import: compressed bytes representations', () => {
  it('should import when compressed data is Uint8Array', async () => {
    const { exported, payload, logicalKey, compressed } = await createCompressedExport();

    const bytes = new Uint8Array(compressed.buffer, compressed.byteOffset, compressed.byteLength);
    const modified = { ...exported, entries: exported.entries.map((entry) => ({ ...entry, data: bytes })) } as any;

    const destRoot = await createTempProjectRoot('ae-1080-dst-');
    const dest = createManager(destRoot);
    await dest.initialize();
    await dest.importState(modified);

    expect(await dest.loadSSOT(logicalKey)).toEqual(payload);

    await dest.shutdown();
    await cleanupProjectRoot(destRoot);
  });

  it('should import when compressed data is ArrayBuffer', async () => {
    const { exported, payload, logicalKey, compressed } = await createCompressedExport();

    const bytes = compressed.buffer.slice(compressed.byteOffset, compressed.byteOffset + compressed.byteLength);
    const modified = { ...exported, entries: exported.entries.map((entry) => ({ ...entry, data: bytes })) } as any;

    const destRoot = await createTempProjectRoot('ae-1080-dst-');
    const dest = createManager(destRoot);
    await dest.initialize();
    await dest.importState(modified);

    expect(await dest.loadSSOT(logicalKey)).toEqual(payload);

    await dest.shutdown();
    await cleanupProjectRoot(destRoot);
  });

  it('should import when compressed data is SharedArrayBuffer', async () => {
    if (typeof SharedArrayBuffer === 'undefined') {
      return;
    }

    const { exported, payload, logicalKey, compressed } = await createCompressedExport();

    const sab = new SharedArrayBuffer(compressed.byteLength);
    new Uint8Array(sab).set(compressed);
    const modified = { ...exported, entries: exported.entries.map((entry) => ({ ...entry, data: sab })) } as any;

    const destRoot = await createTempProjectRoot('ae-1080-dst-');
    const dest = createManager(destRoot);
    await dest.initialize();
    await dest.importState(modified);

    expect(await dest.loadSSOT(logicalKey)).toEqual(payload);

    await dest.shutdown();
    await cleanupProjectRoot(destRoot);
  });
});

