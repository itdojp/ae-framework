import { afterEach, beforeEach, describe, expect, it } from 'vitest';
import { mkdtempSync, readFileSync, rmSync, writeFileSync, mkdirSync, existsSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import { spawnSync } from 'node:child_process';

const repoRoot = process.cwd();
const scriptPath = join(repoRoot, 'scripts', 'formal', 'format-counterexamples.mjs');

function writeJson(path: string, value: unknown): void {
  mkdirSync(dirname(path), { recursive: true });
  writeFileSync(path, JSON.stringify(value, null, 2));
}

function runFormatter(cwd: string) {
  return spawnSync(process.execPath, [scriptPath], {
    cwd,
    encoding: 'utf8',
  });
}

describe('format-counterexamples', () => {
  let workdir: string;

  beforeEach(() => {
    workdir = mkdtempSync(join(tmpdir(), 'ae-format-counterexamples-'));
  });

  afterEach(() => {
    rmSync(workdir, { recursive: true, force: true });
  });

  it('derives GWT summaries from the hermetic formal aggregate before legacy fallback', () => {
    writeJson(join(workdir, 'artifacts', 'hermetic-reports', 'formal', 'summary.json'), {
      timestamp: '2026-05-10T00:00:00.000Z',
      present: { apalache: true },
      apalache: {
        tool: 'apalache',
        status: 'ran',
        counterexamples: [
          {
            schemaVersion: '1.0.0',
            violated: {
              kind: 'INVARIANT',
              name: 'Invariant',
              message: 'allocated <= onHand',
            },
            trace: [
              { index: 0, state: { onHand: 10, allocated: 0 }, action: 'Init' },
              { index: 1, state: { onHand: 10, allocated: 12 }, action: 'Allocate(12)' },
            ],
          },
        ],
      },
    });
    writeJson(join(workdir, 'formal', 'summary.json'), {
      tool: 'tla+',
      result: 'fail',
      counterexamples: [
        {
          property: 'legacy property',
          json: {
            then: { violated: 'legacy property' },
          },
        },
      ],
    });

    const result = runFormatter(workdir);
    expect(result.status, result.stderr || result.stdout).toBe(0);
    expect(result.stdout).toContain('hermetic-formal-aggregate');

    const summary = JSON.parse(
      readFileSync(join(workdir, 'artifacts', 'formal', 'gwt.summary.json'), 'utf8'),
    ) as { source: string; items: Array<{ property: string; gwt: string; json: unknown }> };
    const text = readFileSync(join(workdir, 'artifacts', 'formal', 'gwt.txt'), 'utf8');

    expect(summary.source).toBe('artifacts/hermetic-reports/formal/summary.json');
    expect(summary.items).toHaveLength(1);
    expect(summary.items[0]?.property).toBe('allocated <= onHand');
    expect(summary.items[0]?.gwt).toContain('Given {"onHand":10,"allocated":0}');
    expect(summary.items[0]?.gwt).toContain('When Init -> Allocate(12)');
    expect(summary.items[0]?.gwt).toContain('Then invariant "allocated <= onHand" fails');
    expect(summary.items[0]?.json).toMatchObject({
      violated: { message: 'allocated <= onHand' },
      trace: [{ index: 0 }, { index: 1 }],
    });
    expect(text).toContain('When Init -> Allocate(12)');
    expect(text).not.toContain('legacy property');
  });

  it('keeps legacy formal summary counterexamples as the final fallback', () => {
    writeJson(join(workdir, 'formal', 'summary.json'), {
      tool: 'tla+',
      result: 'fail',
      counterexamples: [
        {
          property: 'legacy invariant',
          json: {
            given: { stock: 1 },
            when: { command: 'reserve', qty: 2 },
            then: { violated: 'legacy invariant' },
          },
        },
      ],
    });

    const result = runFormatter(workdir);
    expect(result.status, result.stderr || result.stdout).toBe(0);
    expect(result.stdout).toContain('legacy-formal-summary');

    const summary = JSON.parse(
      readFileSync(join(workdir, 'artifacts', 'formal', 'gwt.summary.json'), 'utf8'),
    ) as { source: string; items: Array<{ property: string; gwt: string }> };

    expect(summary.source).toBe('formal/summary.json');
    expect(summary.items).toHaveLength(1);
    expect(summary.items[0]?.property).toBe('legacy invariant');
    expect(summary.items[0]?.gwt).toContain('Then invariant "legacy invariant" fails');
  });

  it('discovers formal aggregate tool keys from info.present', () => {
    writeJson(join(workdir, 'artifacts', 'formal', 'formal-aggregate.json'), {
      info: {
        present: {
          tlc: true,
        },
      },
      tlc: {
        counterexamples: [
          {
            violated: {
              kind: 'INVARIANT',
              name: 'InventoryInvariant',
            },
            trace: [
              { index: 0, state: { inventory: 1 }, action: 'Init' },
              { index: 1, state: { inventory: -1 }, action: 'Reserve(2)' },
            ],
          },
        ],
      },
    });

    const result = runFormatter(workdir);
    expect(result.status, result.stderr || result.stdout).toBe(0);
    expect(result.stdout).toContain('formal-aggregate');

    const summary = JSON.parse(
      readFileSync(join(workdir, 'artifacts', 'formal', 'gwt.summary.json'), 'utf8'),
    ) as { source: string; items: Array<{ property: string; gwt: string }> };

    expect(summary.source).toBe('artifacts/formal/formal-aggregate.json');
    expect(summary.items[0]?.property).toBe('InventoryInvariant');
    expect(summary.items[0]?.gwt).toContain('When Init -> Reserve(2)');
  });

  it('exits without writing artifacts when no counterexample source exists', () => {
    const result = runFormatter(workdir);

    expect(result.status, result.stderr || result.stdout).toBe(0);
    expect(result.stdout).toContain('No formal counterexamples found');
    expect(result.stderr).toBe('');
    expect(existsSync(join(workdir, 'artifacts', 'formal', 'gwt.summary.json'))).toBe(false);
  });
});
