import { describe, it, expect, beforeAll, beforeEach, vi } from 'vitest';
import { join } from 'node:path';

const writeFile = vi.fn();
const mkdir = vi.fn();
vi.mock('node:fs/promises', () => ({
  writeFile,
  mkdir,
}));

const sanitizeFilename = (value: string) => value.replace(/[^a-zA-Z0-9-_]/g, '_');

let writeRepro: (name: string, seed: number, data: unknown) => Promise<void>;

beforeAll(async () => {
  ({ writeRepro } = await import('../../../src/testing/repro-writer.js'));
});

beforeEach(() => {
  writeFile.mockReset();
  mkdir.mockReset();
});

describe('writeRepro', () => {
  it('writes JSON literals for names and seeds with special characters', async () => {
    const name = 'weird "name" \\ path\nline';
    const seed = 12345;
    const data = { note: 'line\nbreak', count: 2 };

    await writeRepro(name, seed, data);

    const safeName = sanitizeFilename(name);
    const expectedJsonPath = join('artifacts', 'repros', `${safeName}.repro.json`);
    const expectedPath = join('artifacts', 'repros', `${safeName}.repro.ts`);

    expect(mkdir).toHaveBeenCalledWith('artifacts/repros', { recursive: true });
    expect(writeFile).toHaveBeenCalledTimes(2);
    expect(writeFile).toHaveBeenCalledWith(expectedJsonPath, expect.any(String));
    expect(writeFile).toHaveBeenCalledWith(expectedPath, expect.any(String));

    const jsonBody = writeFile.mock.calls.find((call) => call[0] === expectedJsonPath)?.[1] ?? '';
    const body = writeFile.mock.calls.find((call) => call[0] === expectedPath)?.[1] ?? '';
    const testNameMatch = body.match(/test\(("(?:[^"\\]|\\.)*")/);
    const seedMatch = body.match(/process\.env\.AE_SEED=("(?:[^"\\]|\\.)*")/);
    const dataPathMatch = body.match(/join\(__dirname,\s*("(?:[^"\\]|\\.)*")\)/);

    expect(testNameMatch).not.toBeNull();
    expect(seedMatch).not.toBeNull();
    expect(dataPathMatch).not.toBeNull();
    expect(JSON.parse(testNameMatch?.[1] ?? '""')).toBe(`${name} repro`);
    expect(JSON.parse(seedMatch?.[1] ?? '""')).toBe(String(seed));
    expect(JSON.parse(dataPathMatch?.[1] ?? '""')).toBe(`${safeName}.repro.json`);
    expect(JSON.parse(jsonBody)).toEqual(data);
    expect(body.endsWith(');')).toBe(true);
  });

  it('escapes unsafe characters for code generation', async () => {
    const name = '<tag>\u2028';
    const data = { text: '</script>\u2029' };

    await writeRepro(name, 1, data);

    const safeName = sanitizeFilename(name);
    const expectedJsonPath = join('artifacts', 'repros', `${safeName}.repro.json`);
    const expectedPath = join('artifacts', 'repros', `${safeName}.repro.ts`);
    const jsonBody = writeFile.mock.calls.find((call) => call[0] === expectedJsonPath)?.[1] ?? '';
    const body = writeFile.mock.calls.find((call) => call[0] === expectedPath)?.[1] ?? '';

    expect(body).toContain('\\u003Ctag\\u003E');
    expect(body).toContain('\\u2028');
    expect(JSON.parse(jsonBody)).toEqual(data);
  });

  it('sanitizes unicode names for filenames', async () => {
    const name = '\u30e6\u30cb\u30b3\u30fc\u30c9';
    await writeRepro(name, 0, { ok: true });

    const safeName = sanitizeFilename(name);
    const expectedJsonPath = join('artifacts', 'repros', `${safeName}.repro.json`);
    const expectedPath = join('artifacts', 'repros', `${safeName}.repro.ts`);

    const body = writeFile.mock.calls.find((call) => call[0] === expectedPath)?.[1] ?? '';
    const testNameMatch = body.match(/test\(("(?:[^"\\]|\\.)*")/);

    expect(writeFile).toHaveBeenCalledWith(expectedJsonPath, expect.any(String));
    expect(writeFile).toHaveBeenCalledWith(expectedPath, expect.any(String));
    expect(testNameMatch).not.toBeNull();
    expect(JSON.parse(testNameMatch?.[1] ?? '""')).toBe(`${name} repro`);
  });
});
