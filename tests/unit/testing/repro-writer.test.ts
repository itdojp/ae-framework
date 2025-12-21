import { describe, it, expect, beforeAll, beforeEach, vi } from 'vitest';

const writeFile = vi.fn();
const mkdir = vi.fn();

vi.mock('node:fs/promises', () => ({
  writeFile,
  mkdir
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
    const expectedPath = `artifacts/repros/${safeName}.repro.ts`;

    expect(mkdir).toHaveBeenCalledWith('artifacts/repros', { recursive: true });
    expect(writeFile).toHaveBeenCalledTimes(1);
    expect(writeFile).toHaveBeenCalledWith(expectedPath, expect.any(String));

    const body = writeFile.mock.calls[0]?.[1] ?? '';
    expect(body).toContain(`JSON.parse(${JSON.stringify(JSON.stringify(data))})`);
    expect(body).toContain('test(');
    expect(body).toContain('process.env.AE_SEED=');
    expect(body).toContain('JSON.parse(');
    expect(body.endsWith(');')).toBe(true);
  });

  it('escapes unsafe characters for code generation', async () => {
    const name = '<tag>\u2028';
    const data = { text: '</script>\u2029' };

    await writeRepro(name, 1, data);

    const body = writeFile.mock.calls[0]?.[1] ?? '';
    expect(body).toContain('\\u003Ctag\\u003E');
    expect(body).toContain('\\u2028');
    expect(body).toContain('\\u003C\\u002Fscript\\u003E');
    expect(body).toContain('\\u2029');
  });

  it('sanitizes unicode names for filenames', async () => {
    const name = '\u30e6\u30cb\u30b3\u30fc\u30c9';
    await writeRepro(name, 0, { ok: true });

    const safeName = sanitizeFilename(name);
    const expectedPath = `artifacts/repros/${safeName}.repro.ts`;

    expect(writeFile).toHaveBeenCalledWith(
      expectedPath,
      expect.stringContaining(JSON.stringify(`${name} repro`))
    );
  });
});
