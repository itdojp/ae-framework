import { describe, expect, it } from 'vitest';
import {
  existsSync,
  mkdirSync,
  mkdtempSync,
  readFileSync,
  rmSync,
  writeFileSync,
} from 'node:fs';
import { spawnSync } from 'node:child_process';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';

const inventoryScriptPath = resolve('scripts/testing/test-inventory.mjs');
const freshnessScriptPath = resolve('scripts/coverage/freshness.mjs');

function writeTextFile(rootDir: string, relativePath: string, content: string): string {
  const absolutePath = join(rootDir, relativePath);
  mkdirSync(dirname(absolutePath), { recursive: true });
  writeFileSync(absolutePath, content, 'utf8');
  return absolutePath;
}

function writeCoverageSummary(rootDir: string, gitHead: string | null): void {
  const summary = {
    generatedAt: '2026-05-08T00:00:00.000Z',
    sourcePath: 'coverage/coverage-summary.json',
    git: gitHead ? { head: gitHead } : undefined,
    total: {
      lines: { total: 10, covered: 9, skipped: 0, pct: 90 },
      statements: { total: 20, covered: 18, skipped: 0, pct: 90 },
      functions: { total: 5, covered: 4, skipped: 0, pct: 80 },
      branches: { total: 8, covered: 6, skipped: 0, pct: 75 },
    },
  };
  writeTextFile(rootDir, 'coverage/coverage-summary.json', `${JSON.stringify(summary, null, 2)}\n`);
}

function runNodeScript(scriptPath: string, cwd: string, args: string[] = []) {
  return spawnSync('node', [scriptPath, ...args], {
    cwd,
    encoding: 'utf8',
    env: { ...process.env },
  });
}

function readJsonFile(rootDir: string, relativePath: string) {
  return JSON.parse(readFileSync(join(rootDir, relativePath), 'utf8'));
}

describe('testing inventory and coverage freshness scripts', () => {
  it('generates categorized test inventory with fresh coverage metadata', () => {
    const dir = mkdtempSync(join(tmpdir(), 'test-inventory-fresh-'));

    try {
      writeTextFile(dir, 'tests/unit/foo.test.ts', 'import { it } from "vitest"; it("unit", () => {});');
      writeTextFile(dir, 'tests/contracts/bar.test.ts', 'import { it } from "vitest"; it("contract", () => {});');
      writeTextFile(dir, 'tests/agents/agent-mcp.test.ts', 'import { it } from "vitest"; it("agent", () => {});');
      writeTextFile(dir, 'tests/commands/qa-run.spec.ts', 'import { it } from "vitest"; it("command", () => {});');
      writeTextFile(dir, 'packages/ui/src/button.test.tsx', 'export const Button = () => null;');
      writeTextFile(dir, 'node_modules/pkg/ignored.test.ts', 'throw new Error("must be ignored");');
      writeCoverageSummary(dir, 'abc1234');

      const result = runNodeScript(inventoryScriptPath, dir, ['--head-sha', 'abc1234']);
      expect(result.status).toBe(0);
      expect(result.stderr).toBe('');

      const report = readJsonFile(dir, 'artifacts/testing/test-inventory.json');
      expect(existsSync(join(dir, 'artifacts/testing/test-inventory.md'))).toBe(true);
      expect(report.schemaVersion).toBe('test-inventory/v1');
      expect(report.git.head).toBe('abc1234');
      expect(report.totals.files).toBe(5);
      expect(report.totals.categories).toEqual(
        expect.objectContaining({
          'agent-mcp': 1,
          'cli-command': 1,
          contract: 1,
          unit: 1,
          workspace: 1,
        }),
      );
      expect(report.totals.costClasses).toEqual(expect.objectContaining({ S: 2, 'S-M': 3 }));
      expect(report.files).toEqual(
        expect.arrayContaining([
          expect.objectContaining({ path: 'tests/unit/foo.test.ts', category: 'unit', likelyTarget: 'src/foo.ts' }),
          expect.objectContaining({ path: 'tests/contracts/bar.test.ts', category: 'contract', likelyTarget: 'schema, fixtures, artifact producers' }),
          expect.objectContaining({ path: 'packages/ui/src/button.test.tsx', category: 'workspace', likelyTarget: 'packages/ui' }),
        ]),
      );
      expect(report.files.map((file: { path: string }) => file.path)).not.toContain('node_modules/pkg/ignored.test.ts');
      expect(report.coverageFreshness).toEqual(
        expect.objectContaining({
          schemaVersion: 'coverage-freshness/v1',
          status: 'fresh',
          isFresh: true,
          reportOnly: true,
          summaryGitSha: 'abc1234',
          currentHead: 'abc1234',
          summaryPath: 'coverage/coverage-summary.json',
        }),
      );
      expect(report.coverageFreshness.metrics.lines).toEqual(
        expect.objectContaining({ total: 10, covered: 9, pct: 90 }),
      );
      expect(report.commands).toEqual(
        expect.objectContaining({
          inventory: 'pnpm run testing:inventory',
          coverage: 'pnpm run coverage',
          freshness: 'pnpm run coverage:freshness',
        }),
      );
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  });

  it('reports stale coverage as warning-only and exits successfully', () => {
    const dir = mkdtempSync(join(tmpdir(), 'coverage-freshness-stale-'));

    try {
      writeCoverageSummary(dir, 'oldsha');
      const result = runNodeScript(freshnessScriptPath, dir, ['--head-sha', 'newsha']);
      expect(result.status).toBe(0);
      expect(result.stderr).toContain('warning: coverage summary git SHA oldsha does not match current HEAD newsha');

      const report = readJsonFile(dir, 'artifacts/testing/coverage-freshness.json');
      expect(existsSync(join(dir, 'artifacts/testing/coverage-freshness.md'))).toBe(true);
      expect(report).toEqual(
        expect.objectContaining({
          schemaVersion: 'coverage-freshness/v1',
          status: 'stale',
          isFresh: false,
          reportOnly: true,
          summaryGitSha: 'oldsha',
          currentHead: 'newsha',
          updateCommand: 'pnpm run coverage',
        }),
      );
      expect(report.warnings[0]).toContain('run pnpm run coverage');
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  });


  it('does not treat ambiguous short SHA prefixes as fresh coverage', () => {
    const dir = mkdtempSync(join(tmpdir(), 'coverage-freshness-short-sha-'));

    try {
      writeCoverageSummary(dir, 'a');
      const result = runNodeScript(freshnessScriptPath, dir, [
        '--head-sha',
        'abcdef1234567890abcdef1234567890abcdef12',
      ]);
      expect(result.status).toBe(0);

      const report = readJsonFile(dir, 'artifacts/testing/coverage-freshness.json');
      expect(report).toEqual(
        expect.objectContaining({
          status: 'stale',
          isFresh: false,
          reportOnly: true,
          summaryGitSha: 'a',
        }),
      );
      expect(report.warnings[0]).toContain('does not match current HEAD');
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  });

  it('reports missing coverage summary without failing the command', () => {
    const dir = mkdtempSync(join(tmpdir(), 'coverage-freshness-missing-'));

    try {
      const result = runNodeScript(freshnessScriptPath, dir, ['--head-sha', 'abc1234']);
      expect(result.status).toBe(0);
      expect(result.stderr).toContain('warning: coverage summary is missing');

      const report = readJsonFile(dir, 'artifacts/testing/coverage-freshness.json');
      expect(report).toEqual(
        expect.objectContaining({
          status: 'missing',
          isFresh: false,
          reportOnly: true,
          summaryPath: 'coverage/coverage-summary.json',
        }),
      );
      expect(report.warnings[0]).toContain('run pnpm run coverage');
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  });
});
