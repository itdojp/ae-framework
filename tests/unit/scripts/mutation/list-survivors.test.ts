import { mkdtemp, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { describe, expect, it } from 'vitest';
import {
  collectSurvivors,
  limitSurvivors,
  listSurvivors,
  parseArgs,
} from '../../../../scripts/mutation/list-survivors.mjs';

describe('list-survivors CLI utilities', () => {
  it('parses CLI arguments with defaults', () => {
    expect(parseArgs(['node', 'script.mjs'])).toEqual({
      report: 'reports/mutation/mutation.json',
      limit: Infinity,
    });
  });

  it('parses custom report and limit flags', () => {
    expect(
      parseArgs(['node', 'script.mjs', '--report', 'custom.json', '--limit', '5']),
    ).toEqual({ report: 'custom.json', limit: 5 });
  });

  it('ignores non-surviving mutants when collecting', () => {
    const survivors = collectSurvivors([
      {
        path: 'src/foo.ts',
        mutants: [
          { status: 'Killed', mutatorName: 'RemovedArithmetic' },
          {
            status: 'Survived',
            mutatorName: 'EqualityOperator',
            location: { start: { line: 14, column: 3 } },
          },
        ],
      },
      {
        path: 'src/bar.ts',
        mutants: [
          {
            status: 'Survived',
            mutatorName: 'ConditionalBoundary',
            location: { start: { line: 7 } },
          },
        ],
      },
    ]);

    expect(survivors).toEqual([
      {
        file: 'src/foo.ts',
        mutator: 'EqualityOperator',
        location: { start: { line: 14, column: 3 } },
      },
      {
        file: 'src/bar.ts',
        mutator: 'ConditionalBoundary',
        location: { start: { line: 7 } },
      },
    ]);
  });

  it('limits survivors to the requested length', () => {
    const survivors = [1, 2, 3, 4].map((value) => ({
      file: `dummy-${value}.ts`,
      mutator: 'noop',
      location: null,
    }));

    expect(limitSurvivors(survivors, 2)).toEqual(survivors.slice(0, 2));
    expect(limitSurvivors(survivors, Infinity)).toEqual(survivors);
  });

  it('lists survivors from a mutation report file', async () => {
    const tmp = await mkdtemp(join(tmpdir(), 'survivor-'));
    const reportPath = join(tmp, 'mutation.json');
    const report = {
      files: {
        'src/foo.ts': {
          path: 'src/foo.ts',
          mutants: [
            {
              status: 'Survived',
              mutatorName: 'EqualityOperator',
              location: { start: { line: 10 } },
            },
          ],
        },
        'src/bar.ts': {
          path: 'src/bar.ts',
          mutants: [
            { status: 'Killed', mutatorName: 'UnaryOperator' },
          ],
        },
      },
    };

    await writeFile(reportPath, JSON.stringify(report), 'utf8');

    const survivors = await listSurvivors({ report: reportPath, limit: Infinity });
    expect(survivors).toEqual([
      {
        file: 'src/foo.ts',
        mutator: 'EqualityOperator',
        location: { start: { line: 10 } },
      },
    ]);
  });
});
