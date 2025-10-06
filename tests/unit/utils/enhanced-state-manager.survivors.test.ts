import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import { mkdtemp, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { createHash } from 'node:crypto';
import { EnhancedStateManager } from '../../../src/utils/enhanced-state-manager';

const defaultOptions = {
  databasePath: 'state.db',
  enableCompression: true,
};

describe('EnhancedStateManager survivors coverage', () => {
  let projectRoot: string;

  beforeEach(async () => {
    projectRoot = await mkdtemp(join(tmpdir(), 'ae-enhanced-state-'));
  });

  afterEach(async () => {
    if (projectRoot) {
      await rm(projectRoot, { recursive: true, force: true });
    }
  });

  const createManager = () => new EnhancedStateManager(projectRoot, { ...defaultOptions });

  it('calculateChecksum produces deterministic sha256 hashes', async () => {
    const manager = createManager();
    const calculateChecksum = (manager as unknown as {
      calculateChecksum: (data: unknown) => string;
    }).calculateChecksum.bind(manager);

    const payload = { id: 'demo', stock: 3 };
    const expected = createHash('sha256').update(JSON.stringify(payload)).digest('hex');
    expect(calculateChecksum(payload)).toBe(expected);

    const clone = { id: 'demo', stock: 3 };
    expect(calculateChecksum(clone)).toBe(expected);

    const different = { id: 'demo', stock: 4 };
    expect(calculateChecksum(different)).not.toBe(expected);

    const bufferPayload = Buffer.from('enhanced');
    const bufferExpected = createHash('sha256').update(JSON.stringify(bufferPayload)).digest('hex');
    expect(calculateChecksum(bufferPayload)).toBe(bufferExpected);

    await manager.shutdown();
  });

  it('reviveEntryData leaves compressed buffers untouched', async () => {
    const manager = createManager();
    const reviveEntryData = (manager as unknown as {
      reviveEntryData: (raw: any) => Promise<Buffer | unknown>;
    }).reviveEntryData.bind(manager);

    const rawBuffer = Buffer.from([1, 2, 3]);
    const revived = await reviveEntryData({ compressed: true, data: rawBuffer });
    expect(revived).toBe(rawBuffer);

    await manager.shutdown();
  });

  it('reviveEntryData revives Buffer JSON representation', async () => {
    const manager = createManager();
    const reviveEntryData = (manager as unknown as {
      reviveEntryData: (raw: any) => Promise<Buffer | unknown>;
    }).reviveEntryData.bind(manager);

    const representation = { type: 'Buffer', data: [1, 2, 3, 4] };
    const revived = await reviveEntryData({ compressed: true, data: representation });
    expect(Buffer.isBuffer(revived)).toBe(true);
    expect((revived as Buffer).equals(Buffer.from([1, 2, 3, 4]))).toBe(true);

    await manager.shutdown();
  });

  it('reviveEntryData revives numeric arrays and plain AEIR payloads', async () => {
    const manager = createManager();
    const reviveEntryData = (manager as unknown as {
      reviveEntryData: (raw: any) => Promise<Buffer | unknown>;
    }).reviveEntryData.bind(manager);

    const numericArray = [10, 20, 30];
    const revivedArray = await reviveEntryData({ compressed: true, data: numericArray });
    expect(Buffer.isBuffer(revivedArray)).toBe(true);
    expect((revivedArray as Buffer).equals(Buffer.from(numericArray))).toBe(true);

    const aeirPayload = { id: 'sample', type: 'state' };
    const revivedAeir = await reviveEntryData({ compressed: false, data: aeirPayload });
    expect(revivedAeir).toEqual(aeirPayload);

    await manager.shutdown();
  });
});
