import { describe, expect, it } from 'vitest';
import { mkdtempSync, readFileSync, readdirSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { parse } from 'yaml';
import {
  EnhancedFlakeDetector, runBoundedTestCommand, detectionExitCode,
  SUITE_TIMEOUT_MS, KILL_GRACE_MS,
} from '../../../scripts/enhanced-flake-detector.mjs';

describe('enhanced flake execution deadline', () => {
  it('retains a completed successful execution', async () => {
    const result = await runBoundedTestCommand(process.execPath, ['-e', 'console.log("done")']);
    expect(result).toMatchObject({ status: 'pass', success: true, timedOut: false, exitCode: 0 });
    expect(result.stdout).toContain('done');
  });
  it('retains an actual nonzero test failure', async () => {
    expect(await runBoundedTestCommand(process.execPath, ['-e', 'process.exit(42)']))
      .toMatchObject({ status: 'fail', success: false, exitCode: 42, timedOut: false });
  });
  it('distinguishes an unavailable command from a test failure', async () => {
    expect(await runBoundedTestCommand('/nonexistent-ae-test-command', []))
      .toMatchObject({ status: 'tool-error', success: false, exitCode: null, timedOut: false });
  });
  it('cannot turn a timeout into success even when SIGTERM exits zero', async () => {
    const result = await runBoundedTestCommand(process.execPath,
      ['-e', 'process.on("SIGTERM",()=>process.exit(0));setInterval(()=>{},100)'],
      { timeoutMs: 700, killGraceMs: 100 });
    expect(result).toMatchObject({ status: 'timeout', success: false, timedOut: true, exitCode: 0 });
    expect(result.duration).toBeGreaterThanOrEqual(700);
    expect(result.duration).toBeLessThan(3000);
  });
  it.skipIf(process.platform === 'win32')('kills workers retaining pipes after the wrapper exits', async () => {
    const code = 'const {spawn}=require("node:child_process");const c=spawn(process.execPath,["-e",\'process.on("SIGTERM",()=>{});setInterval(()=>{},100)\'],{stdio:["ignore",1,2]});console.log(c.pid);process.exit(0)';
    const result = await runBoundedTestCommand(process.execPath, ['-e', code], { timeoutMs: 700, killGraceMs: 100 });
    expect(result).toMatchObject({ status: 'timeout', success: false, timedOut: true });
    expect(result.duration).toBeLessThan(3000);
    const pid = Number(result.stdout.trim());
    expect(pid).toBeGreaterThan(0);
    // Linux may briefly retain a reparented zombie; it is not an executing worker.
    if (process.platform === 'linux') {
      try { expect(readFileSync('/proc/' + pid + '/stat', 'utf8').split(') ')[1][0]).toBe('Z'); }
      catch (error: any) { if (error.code !== 'ENOENT') throw error; }
    }
  });
  it('bounds retained output', async () => {
    const result = await runBoundedTestCommand(process.execPath, ['-e', 'process.stdout.write("x".repeat(100000))']);
    expect(result.success).toBe(true);
    expect(result.stdout.length).toBe(65536);
  });
  it.each([0, -1, NaN, 600001])('rejects invalid deadline %s', (timeoutMs) => {
    expect(() => runBoundedTestCommand(process.execPath, [], { timeoutMs })).toThrow('invalid');
  });
  it('preserves timeout/tool-error over environment keyword heuristics', () => {
    const detector = new EnhancedFlakeDetector();
    for (const status of ['timeout', 'tool-error']) {
      expect(detector.analyzeFailurePatterns({ status, stdout: 'CI environment network resource', stderr: '' }).failureType).toBe(status);
    }
  });
  it('keeps failure rate and threshold enforcement unchanged', () => {
    const detector = new EnhancedFlakeDetector({ runs: 3, threshold: 0.15 });
    const stats = detector.calculateStatistics([{success:true}, {success:true}, {success:false}]);
    expect(stats.failureRate).toBe(1 / 3);
    expect(detectionExitCode(stats, detector.threshold)).toBe(1);
    expect(detectionExitCode({ failureRate: 0 }, detector.threshold)).toBe(0);
  });
  it('persists an observed timeout without converting it to environment failure', async () => {
    const root = mkdtempSync(path.join(tmpdir(), 'flake-report-'));
    try {
      const detector = new EnhancedFlakeDetector({ outputDir: root });
      const result = await runBoundedTestCommand(process.execPath, ['-e', 'setInterval(()=>{},100)'], { timeoutMs: 200 });
      const report = await detector.generateReport({
        statistics: detector.calculateStatistics([result]), results: [{...result, run: 1}],
        patternAnalysis: { failureCategories: new Map([['timeout', 1]]), timeDistribution: [result.duration] }, recommendation: [],
      });
      expect(report.results[0]).toMatchObject({ success: false, status: 'timeout', timedOut: true, timeoutMs: 200 });
      expect(report.patternAnalysis.failureCategories).toEqual({ timeout: 1 });
    } finally { rmSync(root, { recursive: true, force: true }); }
  });
  it.skipIf(process.platform === 'win32')('writes failure evidence before exiting nonzero from the CLI', () => {
    const root = mkdtempSync(path.join(tmpdir(), 'flake-cli-'));
    try {
      writeFileSync(path.join(root, 'pnpm'), '#!/bin/sh\nexit 7\n', { mode: 0o700 });
      const output = path.join(root, 'report');
      const run = spawnSync(process.execPath, ['scripts/enhanced-flake-detector.mjs', '--runs', '1', '--output', output], {
        env: { ...process.env, PATH: root + path.delimiter + process.env.PATH }, encoding: 'utf8', timeout: 10000,
      });
      expect(run.status, run.stderr).toBe(1);
      const report = JSON.parse(readFileSync(path.join(output, readdirSync(output)[0]), 'utf8'));
      expect(report.results[0]).toMatchObject({ success: false, exitCode: 7, status: 'fail', timedOut: false, timeoutMs: SUITE_TIMEOUT_MS });
      expect(report.statistics.failures).toBe(1);
    } finally { rmSync(root, { recursive: true, force: true }); }
  });
  it('fits three full attempts inside the workflow budget without changing scope', () => {
    const workflow = parse(readFileSync('.github/workflows/parallel-test-execution.yml', 'utf8'));
    const lane = workflow.jobs['test-matrix'].strategy.matrix.include.find((entry: any) => entry['test-type'] === 'flake-detection');
    const pkg = JSON.parse(readFileSync('package.json', 'utf8'));
    expect(pkg.scripts[lane.command]).toBe('node scripts/enhanced-flake-detector.mjs --runs 3 --threshold 0.15');
    expect(lane.timeout * 60000).toBeGreaterThan(3 * (SUITE_TIMEOUT_MS + KILL_GRACE_MS + 1000) + 60000);
    const retry = workflow.jobs['test-flaky-retry'].steps.find((step: any) => step.run?.includes('pnpm run flake:detect:enhanced:quick'));
    expect(retry['timeout-minutes']).toBe(lane.timeout);
  });
});
