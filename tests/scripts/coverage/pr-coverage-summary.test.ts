import { describe, it, expect } from 'vitest';
import { spawnSync } from 'node:child_process';
import { writeFileSync, mkdirSync } from 'node:fs';
import { join } from 'node:path';

describe('pr-coverage-summary.mjs (dry-run)', () => {
  it('prints summary with effective threshold from label and derived/order lines', () => {
    const cwd = process.cwd();
    const covDir = join(cwd, 'coverage');
    try { mkdirSync(covDir, { recursive: true }); } catch {}
    const covPath = join(covDir, 'coverage-summary.json');
    writeFileSync(covPath, JSON.stringify({ total: { lines: { pct: 83.2 }, functions: { pct: 81 }, branches: { pct: 79.49 }, statements: { pct: 84.0 } } }), 'utf8');

    const event = {
      pull_request: {
        number: 123,
        labels: [ { name: 'coverage:75' } ]
      },
      ref: 'refs/heads/feature/x'
    };
    const eventPath = join(cwd, 'tmp-gh-event.json');
    writeFileSync(eventPath, JSON.stringify(event), 'utf8');

    const env = {
      ...process.env,
      GITHUB_TOKEN: 'test-token',
      GITHUB_REPOSITORY: 'owner/repo',
      GITHUB_EVENT_NAME: 'pull_request',
      GITHUB_EVENT_PATH: eventPath,
      AE_COVERAGE_DRY_RUN: '1',
      COVERAGE_DEFAULT_THRESHOLD: '80'
    } as NodeJS.ProcessEnv;

    const res = spawnSync('node', ['scripts/coverage/pr-coverage-summary.mjs'], { cwd, env, encoding: 'utf8' });
    expect(res.status).toBe(0);
    const out = res.stdout || '';
    expect(out).toContain('AE-COVERAGE-SUMMARY (dry-run)');
    expect(out).toContain('Coverage (lines): 83.2%');
    expect(out).toContain('Metrics: functions=81%, branches=79.5%, statements=84%');
    expect(out).toContain('Threshold (effective): 75%');
    expect(out).toContain('Derived: label > repo var > default');
    // Gate informational line should reflect comparator
    expect(out).toMatch(/Gate: (OK|BELOW) \(83\.2% (>=|<) 75%\)/);
  });
});

