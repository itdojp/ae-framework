import { describe, expect, it } from 'vitest';
import {
  existsSync,
  mkdtempSync,
  mkdirSync,
  readFileSync,
  rmSync,
  writeFileSync,
} from 'node:fs';
import { spawnSync } from 'node:child_process';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';

const scriptPath = resolve('scripts/quality/ts-inventory.mjs');

function writeTextFile(rootDir: string, relativePath: string, content: string): string {
  const absolutePath = join(rootDir, relativePath);
  mkdirSync(dirname(absolutePath), { recursive: true });
  writeFileSync(absolutePath, content, 'utf8');
  return absolutePath;
}

function runInventory(cwd: string, args: string[] = []) {
  return spawnSync('node', [scriptPath, ...args], {
    cwd,
    encoding: 'utf8',
    env: { ...process.env },
  });
}

function readReport(rootDir: string) {
  const reportPath = join(rootDir, 'artifacts', 'metrics', 'ts-inventory.json');
  const report = JSON.parse(readFileSync(reportPath, 'utf8'));
  return { reportPath, report };
}

describe('ts-inventory script', () => {
  it('counts TypeScript inventory metrics and large files', () => {
    const dir = mkdtempSync(join(tmpdir(), 'ts-inventory-counts-'));

    try {
      writeTextFile(
        dir,
        'src/problematic.ts',
        [
          'const value: any = 1;',
          '// @ts-ignore',
          '// @ts-nocheck',
          '/* eslint-disable no-console */',
        ].join('\n'),
      );
      writeTextFile(dir, 'src/clean.ts', 'export const answer = 42;');
      writeTextFile(
        dir,
        'src/large.ts',
        [
          'export const line1 = 1;',
          'export const line2 = 2;',
          'export const line3 = 3;',
          'export const line4 = 4;',
          'export const line5 = 5;',
          'export const line6 = 6;',
        ].join('\n'),
      );

      const result = runInventory(dir, ['--large-file-lines', '5']);
      expect(result.status).toBe(0);

      const { reportPath, report } = readReport(dir);
      expect(existsSync(reportPath)).toBe(true);
      expect(report.totals).toEqual(
        expect.objectContaining({
          files: 3,
          lines: 11,
          any: 1,
          tsIgnore: 1,
          tsNoCheck: 1,
          eslintDisable: 1,
        }),
      );
      expect(report.largeFiles).toEqual([{ path: 'src/large.ts', lines: 6 }]);
      expect(report.issueFiles).toEqual(
        expect.arrayContaining([
          expect.objectContaining({
            path: 'src/problematic.ts',
            any: 1,
            tsIgnore: 1,
            tsNoCheck: 1,
            eslintDisable: 1,
          }),
        ]),
      );
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  });

  it('detects tsIgnore increase from baseline in warn-only mode', () => {
    const dir = mkdtempSync(join(tmpdir(), 'ts-inventory-baseline-warn-'));

    try {
      writeTextFile(dir, 'src/index.ts', ['// @ts-ignore', 'export const value = 1;'].join('\n'));
      const baselinePath = writeTextFile(
        dir,
        'baseline.json',
        `${JSON.stringify({ totals: { tsIgnore: 0 } }, null, 2)}\n`,
      );

      const result = runInventory(dir, ['--baseline', baselinePath]);
      expect(result.status).toBe(0);

      const { report } = readReport(dir);
      expect(report.baselineComparison).toEqual(
        expect.objectContaining({
          baselineTsIgnore: 0,
          currentTsIgnore: 1,
          deltaTsIgnore: 1,
          increased: true,
          enforce: false,
          shouldFail: false,
        }),
      );
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  });

  it('exits with non-zero status when enforce is enabled and tsIgnore increased', () => {
    const dir = mkdtempSync(join(tmpdir(), 'ts-inventory-baseline-enforce-'));

    try {
      writeTextFile(dir, 'src/index.ts', ['// @ts-ignore', 'export const value = 1;'].join('\n'));
      const baselinePath = writeTextFile(
        dir,
        'baseline.json',
        `${JSON.stringify({ totals: { tsIgnore: 0 } }, null, 2)}\n`,
      );

      const result = runInventory(dir, ['--baseline', baselinePath, '--enforce']);
      expect(result.status).toBe(1);
      expect(result.stderr).toContain('enforcement enabled');

      const { report } = readReport(dir);
      expect(report.baselineComparison).toEqual(
        expect.objectContaining({
          increased: true,
          enforce: true,
          shouldFail: true,
        }),
      );
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  });
});
