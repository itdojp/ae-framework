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
    writeFileSync(covPath, JSON.stringify({ total: { lines: { pct: "83.2%" }, functions: { pct: "81%" }, branches: { pct: "79.49%" }, statements: { pct: "84.0%" } } }), 'utf8');

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

  it('handles invalid coverage:<pct> label values and falls back to default', () => {
    const cwd = process.cwd();
    const covDir = join(cwd, 'coverage');
    try { mkdirSync(covDir, { recursive: true }); } catch {}
    const covPath = join(cwd, 'coverage', 'coverage-summary.json');
    writeFileSync(covPath, JSON.stringify({ total: { lines: { pct: 70 } } }), 'utf8');

    const event = {
      pull_request: {
        number: 124,
        labels: [ { name: 'coverage:abc' } ]
      },
      ref: 'refs/heads/feature/y'
    };
    const eventPath = join(cwd, 'tmp-gh-event-invalid.json');
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
    expect(out).toContain('- via label: coverage:abc (invalid, ignored)');
    expect(out).toContain('Threshold (effective): 80%');
  });

  it('treats out-of-range coverage:<pct> label values as invalid', () => {
    const cwd = process.cwd();
    const covDir = join(cwd, 'coverage');
    try { mkdirSync(covDir, { recursive: true }); } catch {}
    const covPath = join(covDir, 'coverage-summary.json');
    writeFileSync(covPath, JSON.stringify({ total: { lines: { pct: 70 } } }), 'utf8');

    const event = {
      pull_request: {
        number: 126,
        labels: [ { name: 'coverage:150' } ]
      },
      ref: 'refs/heads/feature/range'
    };
    const eventPath = join(cwd, 'tmp-gh-event-oob.json');
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
    expect(out).toContain('- via label: coverage:150 (invalid, ignored)');
    expect(out).toContain('Threshold (effective): 80%');
  });

  it('prints n/a and note when coverage summary is missing', () => {
    const cwd = process.cwd();
    // Ensure coverage dir absent or empty for this test; write no file
    const event = {
      pull_request: {
        number: 125,
        labels: []
      },
      ref: 'refs/heads/feature/z'
    };
    const eventPath = join(cwd, 'tmp-gh-event-missing.json');
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
    expect(out).toContain('Coverage (lines): n/a%');
    expect(out).toMatch(/Note: no coverage-summary\.json found/);
  });

  it('uses artifacts/coverage fallback when default path is absent', () => {
    const cwd = process.cwd();
    const artDir = join(cwd, 'artifacts', 'coverage');
    try { mkdirSync(artDir, { recursive: true }); } catch {}
    const covPath = join(artDir, 'coverage-summary.json');
    writeFileSync(covPath, JSON.stringify({ total: { lines: { pct: 86 } } }), 'utf8');

    const event = {
      pull_request: { number: 127, labels: [] },
      ref: 'refs/heads/feature/fallback'
    };
    const eventPath = join(cwd, 'tmp-gh-event-fallback.json');
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
    expect(out).toContain('Coverage (lines): 86%');
    expect(out).toContain('Report (JSON): artifacts/coverage/coverage-summary.json');
    expect(out).not.toMatch(/no coverage-summary\.json found/);
  });

  it('shows Action hint when Gate is BELOW', () => {
    const cwd = process.cwd();
    const covDir = join(cwd, 'coverage');
    try { mkdirSync(covDir, { recursive: true }); } catch {}
    const covPath = join(covDir, 'coverage-summary.json');
    // Set coverage below default threshold
    writeFileSync(covPath, JSON.stringify({ total: { lines: { pct: 60 } } }), 'utf8');

    const event = {
      pull_request: { number: 128, labels: [] },
      ref: 'refs/heads/feature/below'
    };
    const eventPath = join(cwd, 'tmp-gh-event-below.json');
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
    expect(out).toContain('Gate: BELOW');
    expect(out).toContain('Action: add tests to raise coverage or adjust threshold via /coverage <pct>');
  });

  it('shows [non-blocking] when BELOW without enforce/main gating', () => {
    const cwd = process.cwd();
    const covDir = join(cwd, 'coverage');
    try { mkdirSync(covDir, { recursive: true }); } catch {}
    const covPath = join(covDir, 'coverage-summary.json');
    writeFileSync(covPath, JSON.stringify({ total: { lines: { pct: 70 } } }), 'utf8');

    const event = {
      pull_request: { number: 141, labels: [] },
      ref: 'refs/heads/feature/non-blocking'
    };
    const eventPath = join(cwd, 'tmp-gh-event-nonblocking.json');
    writeFileSync(eventPath, JSON.stringify(event), 'utf8');

    const env = {
      ...process.env,
      GITHUB_TOKEN: 'test-token',
      GITHUB_REPOSITORY: 'owner/repo',
      GITHUB_EVENT_NAME: 'pull_request',
      GITHUB_EVENT_PATH: eventPath,
      AE_COVERAGE_DRY_RUN: '1',
      COVERAGE_DEFAULT_THRESHOLD: '80',
      COVERAGE_ENFORCE_MAIN: ''
    } as NodeJS.ProcessEnv;

    const res = spawnSync('node', ['scripts/coverage/pr-coverage-summary.mjs'], { cwd, env, encoding: 'utf8' });
    expect(res.status).toBe(0);
    const out = res.stdout || '';
    expect(out).toMatch(/Gate: BELOW .* \[non-blocking\]/);
    expect(out).toContain('Policy: report-only');
  });

  it('accepts case-insensitive coverage:<pct> label prefix', () => {
    const cwd = process.cwd();
    const covDir = join(cwd, 'coverage');
    try { mkdirSync(covDir, { recursive: true }); } catch {}
    const covPath = join(covDir, 'coverage-summary.json');
    writeFileSync(covPath, JSON.stringify({ total: { lines: { pct: 90 } } }), 'utf8');

    const event = {
      pull_request: { number: 129, labels: [ { name: 'CoVeRaGe:77' } ] },
      ref: 'refs/heads/feature/case'
    };
    const eventPath = join(cwd, 'tmp-gh-event-case.json');
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
    expect(out).toContain('Threshold (effective): 77%');
    expect(out).toContain('- via label: CoVeRaGe:77');
  });

  it('prints repo var line when COVERAGE_DEFAULT_THRESHOLD is set', () => {
    const cwd = process.cwd();
    const covDir = join(cwd, 'coverage');
    try { mkdirSync(covDir, { recursive: true }); } catch {}
    const covPath = join(covDir, 'coverage-summary.json');
    writeFileSync(covPath, JSON.stringify({ total: { lines: { pct: 81 } } }), 'utf8');

    const event = {
      pull_request: { number: 130, labels: [] },
      ref: 'refs/heads/feature/var'
    };
    const eventPath = join(cwd, 'tmp-gh-event-var.json');
    writeFileSync(eventPath, JSON.stringify(event), 'utf8');

    const env = {
      ...process.env,
      GITHUB_TOKEN: 'test-token',
      GITHUB_REPOSITORY: 'owner/repo',
      GITHUB_EVENT_NAME: 'pull_request',
      GITHUB_EVENT_PATH: eventPath,
      AE_COVERAGE_DRY_RUN: '1',
      COVERAGE_DEFAULT_THRESHOLD: '82'
    } as NodeJS.ProcessEnv;

    const res = spawnSync('node', ['scripts/coverage/pr-coverage-summary.mjs'], { cwd, env, encoding: 'utf8' });
    expect(res.status).toBe(0);
    const out = res.stdout || '';
    expect(out).toContain('Threshold (effective): 82%');
    expect(out).toContain('- repo var: COVERAGE_DEFAULT_THRESHOLD=82%');
    expect(out).toContain('- default: 80%');
  });

  it('accepts percent-suffixed repo var (COVERAGE_DEFAULT_THRESHOLD=85%)', () => {
    const cwd = process.cwd();
    const covDir = join(cwd, 'coverage');
    try { mkdirSync(covDir, { recursive: true }); } catch {}
    const covPath = join(covDir, 'coverage-summary.json');
    writeFileSync(covPath, JSON.stringify({ total: { lines: { pct: 90 } } }), 'utf8');

    const event = {
      pull_request: { number: 151, labels: [] },
      ref: 'refs/heads/feature/repovar-percent'
    };
    const eventPath = join(cwd, 'tmp-gh-event-repovar-percent.json');
    writeFileSync(eventPath, JSON.stringify(event), 'utf8');

    const env = {
      ...process.env,
      GITHUB_TOKEN: 'test-token',
      GITHUB_REPOSITORY: 'owner/repo',
      GITHUB_EVENT_NAME: 'pull_request',
      GITHUB_EVENT_PATH: eventPath,
      AE_COVERAGE_DRY_RUN: '1',
      COVERAGE_DEFAULT_THRESHOLD: '85%'
    } as NodeJS.ProcessEnv;

    const res = spawnSync('node', ['scripts/coverage/pr-coverage-summary.mjs'], { cwd, env, encoding: 'utf8' });
    expect(res.status).toBe(0);
    const out = res.stdout || '';
    expect(out).toContain('Threshold (effective): 85%');
    expect(out).toContain('- repo var: COVERAGE_DEFAULT_THRESHOLD=85%');
  });

  it('accepts decimal repo var (COVERAGE_DEFAULT_THRESHOLD=82.5)', () => {
    const cwd = process.cwd();
    const covDir = join(cwd, 'coverage');
    try { mkdirSync(covDir, { recursive: true }); } catch {}
    const covPath = join(covDir, 'coverage-summary.json');
    writeFileSync(covPath, JSON.stringify({ total: { lines: { pct: 90 } } }), 'utf8');

    const event = {
      pull_request: { number: 154, labels: [] },
      ref: 'refs/heads/feature/repovar-decimal'
    };
    const eventPath = join(cwd, 'tmp-gh-event-repovar-decimal.json');
    writeFileSync(eventPath, JSON.stringify(event), 'utf8');

    const env = {
      ...process.env,
      GITHUB_TOKEN: 'test-token',
      GITHUB_REPOSITORY: 'owner/repo',
      GITHUB_EVENT_NAME: 'pull_request',
      GITHUB_EVENT_PATH: eventPath,
      AE_COVERAGE_DRY_RUN: '1',
      COVERAGE_DEFAULT_THRESHOLD: '82.5'
    } as NodeJS.ProcessEnv;

    const res = spawnSync('node', ['scripts/coverage/pr-coverage-summary.mjs'], { cwd, env, encoding: 'utf8' });
    expect(res.status).toBe(0);
    const out = res.stdout || '';
    expect(out).toContain('Threshold (effective): 82.5%');
    expect(out).toContain('- repo var: COVERAGE_DEFAULT_THRESHOLD=82.5%');
  });

  it('falls back to default when repo var is non-numeric', () => {
    const cwd = process.cwd();
    const covDir = join(cwd, 'coverage');
    try { mkdirSync(covDir, { recursive: true }); } catch {}
    const covPath = join(covDir, 'coverage-summary.json');
    writeFileSync(covPath, JSON.stringify({ total: { lines: { pct: 82 } } }), 'utf8');

    const event = {
      pull_request: { number: 147, labels: [] },
      ref: 'refs/heads/feature/repo-var-nan'
    };
    const eventPath = join(cwd, 'tmp-gh-event-repovar-nan.json');
    writeFileSync(eventPath, JSON.stringify(event), 'utf8');

    const env = {
      ...process.env,
      GITHUB_TOKEN: 'test-token',
      GITHUB_REPOSITORY: 'owner/repo',
      GITHUB_EVENT_NAME: 'pull_request',
      GITHUB_EVENT_PATH: eventPath,
      AE_COVERAGE_DRY_RUN: '1',
      COVERAGE_DEFAULT_THRESHOLD: 'abc'
    } as NodeJS.ProcessEnv;

    const res = spawnSync('node', ['scripts/coverage/pr-coverage-summary.mjs'], { cwd, env, encoding: 'utf8' });
    expect(res.status).toBe(0);
    const out = res.stdout || '';
    expect(out).toContain('Threshold (effective): 80%');
    expect(out).toContain('Source: default');
    expect(out).toContain('- repo var: COVERAGE_DEFAULT_THRESHOLD=n/a%');
    expect(out).toContain('- default: 80%');
  });

  it('falls back when repo var is out of range and notes invalid', () => {
    const cwd = process.cwd();
    const covDir = join(cwd, 'coverage');
    try { mkdirSync(covDir, { recursive: true }); } catch {}
    const covPath = join(covDir, 'coverage-summary.json');
    writeFileSync(covPath, JSON.stringify({ total: { lines: { pct: 82 } } }), 'utf8');

    const event = {
      pull_request: { number: 148, labels: [] },
      ref: 'refs/heads/feature/repovar-oob'
    };
    const eventPath = join(cwd, 'tmp-gh-event-repovar-oob.json');
    writeFileSync(eventPath, JSON.stringify(event), 'utf8');

    const env = {
      ...process.env,
      GITHUB_TOKEN: 'test-token',
      GITHUB_REPOSITORY: 'owner/repo',
      GITHUB_EVENT_NAME: 'pull_request',
      GITHUB_EVENT_PATH: eventPath,
      AE_COVERAGE_DRY_RUN: '1',
      COVERAGE_DEFAULT_THRESHOLD: '150'
    } as NodeJS.ProcessEnv;

    const res = spawnSync('node', ['scripts/coverage/pr-coverage-summary.mjs'], { cwd, env, encoding: 'utf8' });
    expect(res.status).toBe(0);
    const out = res.stdout || '';
    expect(out).toContain('Threshold (effective): 80%');
    expect(out).toContain('Source: default');
    expect(out).toContain('- repo var: COVERAGE_DEFAULT_THRESHOLD=150% (invalid, ignored)');
    expect(out).toContain('- default: 80%');
  });

  it('falls back when repo var is negative and notes invalid', () => {
    const cwd = process.cwd();
    const covDir = join(cwd, 'coverage');
    try { mkdirSync(covDir, { recursive: true }); } catch {}
    const covPath = join(covDir, 'coverage-summary.json');
    writeFileSync(covPath, JSON.stringify({ total: { lines: { pct: 82 } } }), 'utf8');

    const event = {
      pull_request: { number: 163, labels: [] },
      ref: 'refs/heads/feature/repovar-neg'
    };
    const eventPath = join(cwd, 'tmp-gh-event-repovar-neg.json');
    writeFileSync(eventPath, JSON.stringify(event), 'utf8');

    const env = {
      ...process.env,
      GITHUB_TOKEN: 'test-token',
      GITHUB_REPOSITORY: 'owner/repo',
      GITHUB_EVENT_NAME: 'pull_request',
      GITHUB_EVENT_PATH: eventPath,
      AE_COVERAGE_DRY_RUN: '1',
      COVERAGE_DEFAULT_THRESHOLD: '-5'
    } as NodeJS.ProcessEnv;

    const res = spawnSync('node', ['scripts/coverage/pr-coverage-summary.mjs'], { cwd, env, encoding: 'utf8' });
    expect(res.status).toBe(0);
    const out = res.stdout || '';
    expect(out).toContain('Threshold (effective): 80%');
    expect(out).toContain('- repo var: COVERAGE_DEFAULT_THRESHOLD=-5% (invalid, ignored)');
    expect(out).toContain('Source: default');
  });

  it('falls back to default when both label and repo var are invalid', () => {
    const cwd = process.cwd();
    const covDir = join(cwd, 'coverage');
    try { mkdirSync(covDir, { recursive: true }); } catch {}
    const covPath = join(covDir, 'coverage-summary.json');
    writeFileSync(covPath, JSON.stringify({ total: { lines: { pct: 78 } } }), 'utf8');

    const event = {
      pull_request: { number: 150, labels: [ { name: 'coverage:xyz' } ] },
      ref: 'refs/heads/feature/both-invalid'
    };
    const eventPath = join(cwd, 'tmp-gh-event-both-invalid.json');
    writeFileSync(eventPath, JSON.stringify(event), 'utf8');

    const env = {
      ...process.env,
      GITHUB_TOKEN: 'test-token',
      GITHUB_REPOSITORY: 'owner/repo',
      GITHUB_EVENT_NAME: 'pull_request',
      GITHUB_EVENT_PATH: eventPath,
      AE_COVERAGE_DRY_RUN: '1',
      COVERAGE_DEFAULT_THRESHOLD: 'abc'
    } as NodeJS.ProcessEnv;

    const res = spawnSync('node', ['scripts/coverage/pr-coverage-summary.mjs'], { cwd, env, encoding: 'utf8' });
    expect(res.status).toBe(0);
    const out = res.stdout || '';
    expect(out).toContain('- via label: coverage:xyz (invalid, ignored)');
    expect(out).toContain('- repo var: COVERAGE_DEFAULT_THRESHOLD=n/a% (invalid, ignored)');
    expect(out).toContain('Threshold (effective): 80%');
    expect(out).toMatch(/Gate: (OK|BELOW) \(78% (>=|<) 80%\)/);
  });

  it('uses repo var when label invalid but repo var valid', () => {
    const cwd = process.cwd();
    const covDir = join(cwd, 'coverage');
    try { mkdirSync(covDir, { recursive: true }); } catch {}
    const covPath = join(covDir, 'coverage-summary.json');
    writeFileSync(covPath, JSON.stringify({ total: { lines: { pct: 79 } } }), 'utf8');

    const event = {
      pull_request: { number: 149, labels: [ { name: 'coverage:abc' } ] },
      ref: 'refs/heads/feature/label-invalid-repovar-valid'
    };
    const eventPath = join(cwd, 'tmp-gh-event-labelinvalid-repovar.json');
    writeFileSync(eventPath, JSON.stringify(event), 'utf8');

    const env = {
      ...process.env,
      GITHUB_TOKEN: 'test-token',
      GITHUB_REPOSITORY: 'owner/repo',
      GITHUB_EVENT_NAME: 'pull_request',
      GITHUB_EVENT_PATH: eventPath,
      AE_COVERAGE_DRY_RUN: '1',
      COVERAGE_DEFAULT_THRESHOLD: '75'
    } as NodeJS.ProcessEnv;

    const res = spawnSync('node', ['scripts/coverage/pr-coverage-summary.mjs'], { cwd, env, encoding: 'utf8' });
    expect(res.status).toBe(0);
    const out = res.stdout || '';
    expect(out).toContain('- via label: coverage:abc (invalid, ignored)');
    expect(out).toContain('- repo var: COVERAGE_DEFAULT_THRESHOLD=75%');
    expect(out).toContain('Threshold (effective): 75%');
    expect(out).toContain('Source: repo var');
    expect(out).toMatch(/Gate: (OK|BELOW) \(79% (>=|<) 75%\)/);
  });

  it('defaults to 80 when no label and no repo var are set', () => {
    const cwd = process.cwd();
    const covDir = join(cwd, 'coverage');
    try { mkdirSync(covDir, { recursive: true }); } catch {}
    const covPath = join(covDir, 'coverage-summary.json');
    writeFileSync(covPath, JSON.stringify({ total: { lines: { pct: 81 } } }), 'utf8');

    const event = {
      pull_request: { number: 146, labels: [] },
      ref: 'refs/heads/feature/default80'
    };
    const eventPath = join(cwd, 'tmp-gh-event-default80.json');
    writeFileSync(eventPath, JSON.stringify(event), 'utf8');

    const env = {
      ...process.env,
      GITHUB_TOKEN: 'test-token',
      GITHUB_REPOSITORY: 'owner/repo',
      GITHUB_EVENT_NAME: 'pull_request',
      GITHUB_EVENT_PATH: eventPath,
      AE_COVERAGE_DRY_RUN: '1'
    } as NodeJS.ProcessEnv;

    const res = spawnSync('node', ['scripts/coverage/pr-coverage-summary.mjs'], { cwd, env, encoding: 'utf8' });
    expect(res.status).toBe(0);
    const out = res.stdout || '';
    expect(out).toContain('Threshold (effective): 80%');
    expect(out).toContain('Source: default');
    expect(out).toContain('- default: 80%');
  });

  it('adds note when summary exists but total.lines.pct is missing', () => {
    const cwd = process.cwd();
    const covDir = join(cwd, 'coverage');
    try { mkdirSync(covDir, { recursive: true }); } catch {}
    const covPath = join(covDir, 'coverage-summary.json');
    // Write summary without total.lines.pct
    writeFileSync(covPath, JSON.stringify({ total: { statements: { pct: 90 } } }), 'utf8');

    const event = {
      pull_request: { number: 147, labels: [] },
      ref: 'refs/heads/feature/missing-lines-pct'
    };
    const eventPath = join(cwd, 'tmp-gh-event-missing-lines.json');
    writeFileSync(eventPath, JSON.stringify(event), 'utf8');

    const env = {
      ...process.env,
      GITHUB_TOKEN: 'test-token',
      GITHUB_REPOSITORY: 'owner/repo',
      GITHUB_EVENT_NAME: 'pull_request',
      GITHUB_EVENT_PATH: eventPath,
      AE_COVERAGE_DRY_RUN: '1'
    } as NodeJS.ProcessEnv;

    const res = spawnSync('node', ['scripts/coverage/pr-coverage-summary.mjs'], { cwd, env, encoding: 'utf8' });
    expect(res.status).toBe(0);
    const out = res.stdout || '';
    expect(out).toContain('Coverage (lines): n/a%');
    expect(out).toContain('Note: total.lines.pct not found or invalid in coverage summary');
  });

  it('uses last coverage label when multiple labels are present', () => {
    const cwd = process.cwd();
    const covDir = join(cwd, 'coverage');
    try { mkdirSync(covDir, { recursive: true }); } catch {}
    const covPath = join(covDir, 'coverage-summary.json');
    writeFileSync(covPath, JSON.stringify({ total: { lines: { pct: 90 } } }), 'utf8');

    const event = {
      pull_request: { number: 132, labels: [ { name: 'coverage:70' }, { name: 'coverage:88' } ] },
      ref: 'refs/heads/feature/multi'
    };
    const eventPath = join(cwd, 'tmp-gh-event-multi.json');
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
    expect(out).toContain('Threshold (effective): 88%');
    expect(out).toContain('- via label: coverage:88');
  });

  it('last-wins with mixed formatting (CoVeRaGe: 77 % then coverage:88)', () => {
    const cwd = process.cwd();
    const covDir = join(cwd, 'coverage');
    try { mkdirSync(covDir, { recursive: true }); } catch {}
    const covPath = join(covDir, 'coverage-summary.json');
    writeFileSync(covPath, JSON.stringify({ total: { lines: { pct: 90 } } }), 'utf8');

    const event = {
      pull_request: { number: 145, labels: [ { name: 'CoVeRaGe: 77 %' }, { name: 'coverage:88' } ] },
      ref: 'refs/heads/feature/mixed-last-wins'
    };
    const eventPath = join(cwd, 'tmp-gh-event-mixed-last.json');
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
    expect(out).toContain('Threshold (effective): 88%');
    expect(out).toContain('- via label: coverage:88');
  });

  it('last-wins among three labels with middle invalid', () => {
    const cwd = process.cwd();
    const covDir = join(cwd, 'coverage');
    try { mkdirSync(covDir, { recursive: true }); } catch {}
    const covPath = join(covDir, 'coverage-summary.json');
    writeFileSync(covPath, JSON.stringify({ total: { lines: { pct: 92 } } }), 'utf8');

    const event = {
      pull_request: { number: 162, labels: [ { name: 'coverage:70' }, { name: 'coverage:abc' }, { name: 'coverage:85%' } ] },
      ref: 'refs/heads/feature/three-labels'
    };
    const eventPath = join(cwd, 'tmp-gh-event-three-labels.json');
    writeFileSync(eventPath, JSON.stringify(event), 'utf8');

    const env = {
      ...process.env,
      GITHUB_TOKEN: 'test-token',
      GITHUB_REPOSITORY: 'owner/repo',
      GITHUB_EVENT_NAME: 'pull_request',
      GITHUB_EVENT_PATH: eventPath,
      AE_COVERAGE_DRY_RUN: '1'
    } as NodeJS.ProcessEnv;

    const res = spawnSync('node', ['scripts/coverage/pr-coverage-summary.mjs'], { cwd, env, encoding: 'utf8' });
    expect(res.status).toBe(0);
    const out = res.stdout || '';
    expect(out).toContain('Threshold (effective): 85%');
    expect(out).toContain('Source: label');
    expect(out).toContain('- via label: coverage:85%');
  });

  it('uses last label even if invalid (falls back and notes invalid)', () => {
    const cwd = process.cwd();
    const covDir = join(cwd, 'coverage');
    try { mkdirSync(covDir, { recursive: true }); } catch {}
    const covPath = join(covDir, 'coverage-summary.json');
    writeFileSync(covPath, JSON.stringify({ total: { lines: { pct: 90 } } }), 'utf8');

    const event = {
      pull_request: { number: 134, labels: [ { name: 'coverage:85' }, { name: 'coverage:abc' } ] },
      ref: 'refs/heads/feature/last-invalid'
    };
    const eventPath = join(cwd, 'tmp-gh-event-last-invalid.json');
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
    expect(out).toContain('- via label: coverage:abc (invalid, ignored)');
    expect(out).toContain('Threshold (effective): 80%');
  });

  it('accepts decimal threshold in label (e.g., coverage:82.5)', () => {
    const cwd = process.cwd();
    const covDir = join(cwd, 'coverage');
    try { mkdirSync(covDir, { recursive: true }); } catch {}
    const covPath = join(covDir, 'coverage-summary.json');
    writeFileSync(covPath, JSON.stringify({ total: { lines: { pct: 83 } } }), 'utf8');

    const event = {
      pull_request: { number: 133, labels: [ { name: 'coverage:82.5' } ] },
      ref: 'refs/heads/feature/decimal'
    };
    const eventPath = join(cwd, 'tmp-gh-event-decimal.json');
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
    expect(out).toContain('Threshold (effective): 82.5%');
    expect(out).toContain('- via label: coverage:82.5');
  });

  it('accepts labels array as strings (not objects)', () => {
    const cwd = process.cwd();
    const covDir = join(cwd, 'coverage');
    try { mkdirSync(covDir, { recursive: true }); } catch {}
    const covPath = join(covDir, 'coverage-summary.json');
    writeFileSync(covPath, JSON.stringify({ total: { lines: { pct: 88 } } }), 'utf8');

    const event = {
      pull_request: { number: 152, labels: [ 'coverage:85' ] },
      ref: 'refs/heads/feature/labels-strings'
    };
    const eventPath = join(cwd, 'tmp-gh-event-labels-strings.json');
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
    expect(out).toContain('Threshold (effective): 85%');
    expect(out).toContain('Source: label');
    expect(out).toContain('- via label: coverage:85');
  });

  it('omits Metrics line when functions/branches/statements are absent', () => {
    const cwd = process.cwd();
    const covDir = join(cwd, 'coverage');
    try { mkdirSync(covDir, { recursive: true }); } catch {}
    const covPath = join(covDir, 'coverage-summary.json');
    // Only lines present; others missing
    writeFileSync(covPath, JSON.stringify({ total: { lines: { pct: 88 } } }), 'utf8');

    const event = {
      pull_request: { number: 155, labels: [] },
      ref: 'refs/heads/feature/no-metrics'
    };
    const eventPath = join(cwd, 'tmp-gh-event-no-metrics.json');
    writeFileSync(eventPath, JSON.stringify(event), 'utf8');

    const env = {
      ...process.env,
      GITHUB_TOKEN: 'test-token',
      GITHUB_REPOSITORY: 'owner/repo',
      GITHUB_EVENT_NAME: 'pull_request',
      GITHUB_EVENT_PATH: eventPath,
      AE_COVERAGE_DRY_RUN: '1'
    } as NodeJS.ProcessEnv;

    const res = spawnSync('node', ['scripts/coverage/pr-coverage-summary.mjs'], { cwd, env, encoding: 'utf8' });
    expect(res.status).toBe(0);
    const out = res.stdout || '';
    expect(out).toContain('Coverage (lines): 88%');
    expect(out).not.toContain('Metrics:');
  });

  it('omits Metrics when function/branch/statement pct are invalid strings', () => {
    const cwd = process.cwd();
    const covDir = join(cwd, 'coverage');
    try { mkdirSync(covDir, { recursive: true }); } catch {}
    const covPath = join(covDir, 'coverage-summary.json');
    // Provide invalid strings for non-lines metrics
    writeFileSync(
      covPath,
      JSON.stringify({ total: { lines: { pct: 87 }, functions: { pct: 'N/A' }, branches: { pct: '??' }, statements: { pct: 'bad' } } }),
      'utf8'
    );

    const event = {
      pull_request: { number: 156, labels: [] },
      ref: 'refs/heads/feature/metrics-invalid'
    };
    const eventPath = join(cwd, 'tmp-gh-event-metrics-invalid.json');
    writeFileSync(eventPath, JSON.stringify(event), 'utf8');

    const env = {
      ...process.env,
      GITHUB_TOKEN: 'test-token',
      GITHUB_REPOSITORY: 'owner/repo',
      GITHUB_EVENT_NAME: 'pull_request',
      GITHUB_EVENT_PATH: eventPath,
      AE_COVERAGE_DRY_RUN: '1'
    } as NodeJS.ProcessEnv;

    const res = spawnSync('node', ['scripts/coverage/pr-coverage-summary.mjs'], { cwd, env, encoding: 'utf8' });
    expect(res.status).toBe(0);
    const out = res.stdout || '';
    expect(out).toContain('Coverage (lines): 87%');
    expect(out).not.toContain('Metrics:');
  });

  it('includes Metrics when lines is missing but other metrics are valid', () => {
    const cwd = process.cwd();
    const covDir = join(cwd, 'coverage');
    try { mkdirSync(covDir, { recursive: true }); } catch {}
    const covPath = join(covDir, 'coverage-summary.json');
    // No lines.pct but valid functions/branches/statements
    writeFileSync(
      covPath,
      JSON.stringify({ total: { functions: { pct: 81 }, branches: { pct: 79.5 }, statements: { pct: 84 } } }),
      'utf8'
    );

    const event = {
      pull_request: { number: 157, labels: [] },
      ref: 'refs/heads/feature/metrics-only'
    };
    const eventPath = join(cwd, 'tmp-gh-event-metrics-only.json');
    writeFileSync(eventPath, JSON.stringify(event), 'utf8');

    const env = {
      ...process.env,
      GITHUB_TOKEN: 'test-token',
      GITHUB_REPOSITORY: 'owner/repo',
      GITHUB_EVENT_NAME: 'pull_request',
      GITHUB_EVENT_PATH: eventPath,
      AE_COVERAGE_DRY_RUN: '1'
    } as NodeJS.ProcessEnv;

    const res = spawnSync('node', ['scripts/coverage/pr-coverage-summary.mjs'], { cwd, env, encoding: 'utf8' });
    expect(res.status).toBe(0);
    const out = res.stdout || '';
    expect(out).toContain('Coverage (lines): n/a%');
    expect(out).toContain('Metrics: functions=81%, branches=79.5%, statements=84%');
  });

  it('shows n/a and note when lines.pct is an invalid string, but prints Metrics for other valid fields', () => {
    const cwd = process.cwd();
    const covDir = join(cwd, 'coverage');
    try { mkdirSync(covDir, { recursive: true }); } catch {}
    const covPath = join(covDir, 'coverage-summary.json');
    writeFileSync(
      covPath,
      JSON.stringify({ total: { lines: { pct: 'N/A' }, functions: { pct: 80 }, branches: { pct: 75 }, statements: { pct: 82 } } }),
      'utf8'
    );

    const event = {
      pull_request: { number: 160, labels: [] },
      ref: 'refs/heads/feature/lines-invalid'
    };
    const eventPath = join(cwd, 'tmp-gh-event-lines-invalid.json');
    writeFileSync(eventPath, JSON.stringify(event), 'utf8');

    const env = {
      ...process.env,
      GITHUB_TOKEN: 'test-token',
      GITHUB_REPOSITORY: 'owner/repo',
      GITHUB_EVENT_NAME: 'pull_request',
      GITHUB_EVENT_PATH: eventPath,
      AE_COVERAGE_DRY_RUN: '1'
    } as NodeJS.ProcessEnv;

    const res = spawnSync('node', ['scripts/coverage/pr-coverage-summary.mjs'], { cwd, env, encoding: 'utf8' });
    expect(res.status).toBe(0);
    const out = res.stdout || '';
    expect(out).toContain('Coverage (lines): n/a%');
    expect(out).toContain('Note: total.lines.pct not found or invalid in coverage summary');
    expect(out).toContain('Metrics: functions=80%, branches=75%, statements=82%');
  });

  it('honors AE_COVERAGE_SUMMARY_PATH override when present', () => {
    const cwd = process.cwd();
    const customDir = join(cwd, 'custom');
    try { mkdirSync(customDir, { recursive: true }); } catch {}
    const covPath = join(customDir, 'summary.json');
    writeFileSync(covPath, JSON.stringify({ total: { lines: { pct: 91 } } }), 'utf8');

    const event = {
      pull_request: { number: 158, labels: [] },
      ref: 'refs/heads/feature/override'
    };
    const eventPath = join(cwd, 'tmp-gh-event-override.json');
    writeFileSync(eventPath, JSON.stringify(event), 'utf8');

    const env = {
      ...process.env,
      GITHUB_TOKEN: 'test-token',
      GITHUB_REPOSITORY: 'owner/repo',
      GITHUB_EVENT_NAME: 'pull_request',
      GITHUB_EVENT_PATH: eventPath,
      AE_COVERAGE_DRY_RUN: '1',
      AE_COVERAGE_SUMMARY_PATH: 'custom/summary.json'
    } as NodeJS.ProcessEnv;

    const res = spawnSync('node', ['scripts/coverage/pr-coverage-summary.mjs'], { cwd, env, encoding: 'utf8' });
    expect(res.status).toBe(0);
    const out = res.stdout || '';
    expect(out).toContain('Coverage (lines): 91%');
    expect(out).toContain('Report (JSON): custom/summary.json');
  });

  it('hints artifacts HTML report when present', () => {
    const cwd = process.cwd();
    const artCov = join(cwd, 'artifacts', 'coverage');
    try { mkdirSync(artCov, { recursive: true }); } catch {}
    const htmlPath = join(artCov, 'index.html');
    writeFileSync(htmlPath, '<html></html>', 'utf8');
    const covPath = join(cwd, 'coverage', 'coverage-summary.json');
    try { mkdirSync(join(cwd, 'coverage'), { recursive: true }); } catch {}
    writeFileSync(covPath, JSON.stringify({ total: { lines: { pct: 90 } } }), 'utf8');

    const event = {
      pull_request: { number: 161, labels: [] },
      ref: 'refs/heads/feature/html-hint'
    };
    const eventPath = join(cwd, 'tmp-gh-event-html-hint.json');
    writeFileSync(eventPath, JSON.stringify(event), 'utf8');

    const env = {
      ...process.env,
      GITHUB_TOKEN: 'test-token',
      GITHUB_REPOSITORY: 'owner/repo',
      GITHUB_EVENT_NAME: 'pull_request',
      GITHUB_EVENT_PATH: eventPath,
      AE_COVERAGE_DRY_RUN: '1'
    } as NodeJS.ProcessEnv;

    const res = spawnSync('node', ['scripts/coverage/pr-coverage-summary.mjs'], { cwd, env, encoding: 'utf8' });
    expect(res.status).toBe(0);
    const out = res.stdout || '';
    expect(out).toContain('Report (HTML): artifacts/coverage/index.html');
  });

  it('prints note when AE_COVERAGE_SUMMARY_PATH is set but file missing', () => {
    const cwd = process.cwd();
    const event = {
      pull_request: { number: 159, labels: [] },
      ref: 'refs/heads/feature/override-missing'
    };
    const eventPath = join(cwd, 'tmp-gh-event-override-missing.json');
    writeFileSync(eventPath, JSON.stringify(event), 'utf8');

    const env = {
      ...process.env,
      GITHUB_TOKEN: 'test-token',
      GITHUB_REPOSITORY: 'owner/repo',
      GITHUB_EVENT_NAME: 'pull_request',
      GITHUB_EVENT_PATH: eventPath,
      AE_COVERAGE_DRY_RUN: '1',
      AE_COVERAGE_SUMMARY_PATH: 'custom/missing.json'
    } as NodeJS.ProcessEnv;

    const res = spawnSync('node', ['scripts/coverage/pr-coverage-summary.mjs'], { cwd, env, encoding: 'utf8' });
    expect(res.status).toBe(0);
    const out = res.stdout || '';
    expect(out).toMatch(/override path 'custom\/missing\.json' not found/);
  });

  it('skip has precedence over dry-run (prints skip note only)', () => {
    const cwd = process.cwd();
    const env = {
      ...process.env,
      AE_COVERAGE_SKIP_COMMENT: '1',
      AE_COVERAGE_DRY_RUN: '1'
    } as NodeJS.ProcessEnv;

    const res = spawnSync('node', ['scripts/coverage/pr-coverage-summary.mjs'], { cwd, env, encoding: 'utf8' });
    expect(res.status).toBe(0);
    const out = res.stdout || '';
    expect(out).toContain('AE_COVERAGE_SKIP_COMMENT');
    expect(out).not.toContain('AE-COVERAGE-SUMMARY (dry-run)');
  });

  it('override path with invalid JSON → n/a and hint', () => {
    const cwd = process.cwd();
    const customDir = join(cwd, 'custom2');
    try { mkdirSync(customDir, { recursive: true }); } catch {}
    const covPath = join(customDir, 'summary.json');
    // Write invalid JSON
    writeFileSync(covPath, '{ total: ', 'utf8');

    const event = {
      pull_request: { number: 166, labels: [] },
      ref: 'refs/heads/feature/override-invalid-json'
    };
    const eventPath = join(cwd, 'tmp-gh-event-override-invalid.json');
    writeFileSync(eventPath, JSON.stringify(event), 'utf8');

    const env = {
      ...process.env,
      GITHUB_TOKEN: 'test-token',
      GITHUB_REPOSITORY: 'owner/repo',
      GITHUB_EVENT_NAME: 'pull_request',
      GITHUB_EVENT_PATH: eventPath,
      AE_COVERAGE_DRY_RUN: '1',
      AE_COVERAGE_SUMMARY_PATH: 'custom2/summary.json'
    } as NodeJS.ProcessEnv;

    const res = spawnSync('node', ['scripts/coverage/pr-coverage-summary.mjs'], { cwd, env, encoding: 'utf8' });
    expect(res.status).toBe(0);
    const out = res.stdout || '';
    expect(out).toContain('Coverage (lines): n/a%');
    expect(out).toContain('Report (JSON): custom2/summary.json');
  });

  it('parses percent-suffixed label value (coverage:85%)', () => {
    const cwd = process.cwd();
    const covDir = join(cwd, 'coverage');
    try { mkdirSync(covDir, { recursive: true }); } catch {}
    const covPath = join(covDir, 'coverage-summary.json');
    writeFileSync(covPath, JSON.stringify({ total: { lines: { pct: 90 } } }), 'utf8');

    const event = {
      pull_request: { number: 135, labels: [ { name: 'coverage:85%' } ] },
      ref: 'refs/heads/feature/percent'
    };
    const eventPath = join(cwd, 'tmp-gh-event-percent.json');
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
    expect(out).toContain('Threshold (effective): 85%');
    expect(out).toContain('- via label: coverage:85%');
  });

  it('parses percent-suffixed label value with space (coverage: 85 %)', () => {
    const cwd = process.cwd();
    const covDir = join(cwd, 'coverage');
    try { mkdirSync(covDir, { recursive: true }); } catch {}
    const covPath = join(covDir, 'coverage-summary.json');
    writeFileSync(covPath, JSON.stringify({ total: { lines: { pct: 90 } } }), 'utf8');

    const event = {
      pull_request: { number: 138, labels: [ { name: 'coverage: 85 %' } ] },
      ref: 'refs/heads/feature/percent-space'
    };
    const eventPath = join(cwd, 'tmp-gh-event-percent-space.json');
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
    expect(out).toContain('Threshold (effective): 85%');
    expect(out).toContain('- via label: coverage: 85 %');
  });

  it('treats empty coverage label value as invalid (coverage:)', () => {
    const cwd = process.cwd();
    const covDir = join(cwd, 'coverage');
    try { mkdirSync(covDir, { recursive: true }); } catch {}
    const covPath = join(covDir, 'coverage-summary.json');
    writeFileSync(covPath, JSON.stringify({ total: { lines: { pct: 72 } } }), 'utf8');

    const event = {
      pull_request: { number: 142, labels: [ { name: 'coverage:' } ] },
      ref: 'refs/heads/feature/empty'
    };
    const eventPath = join(cwd, 'tmp-gh-event-empty.json');
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
    expect(out).toContain('- via label: coverage: (invalid, ignored)');
    expect(out).toContain('Threshold (effective): 80%');
  });

  it('treats negative label values as invalid and falls back', () => {
    const cwd = process.cwd();
    const covDir = join(cwd, 'coverage');
    try { mkdirSync(covDir, { recursive: true }); } catch {}
    const covPath = join(covDir, 'coverage-summary.json');
    writeFileSync(covPath, JSON.stringify({ total: { lines: { pct: 70 } } }), 'utf8');

    const event = {
      pull_request: { number: 139, labels: [ { name: 'coverage:-5' } ] },
      ref: 'refs/heads/feature/neg'
    };
    const eventPath = join(cwd, 'tmp-gh-event-neg.json');
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
    expect(out).toContain('- via label: coverage:-5 (invalid, ignored)');
    expect(out).toContain('Threshold (effective): 80%');
  });

  it('accepts space before colon in label (coverage :85)', () => {
    const cwd = process.cwd();
    const covDir = join(cwd, 'coverage');
    try { mkdirSync(covDir, { recursive: true }); } catch {}
    const covPath = join(covDir, 'coverage-summary.json');
    writeFileSync(covPath, JSON.stringify({ total: { lines: { pct: 90 } } }), 'utf8');

    const event = {
      pull_request: { number: 164, labels: [ { name: 'coverage :85' } ] },
      ref: 'refs/heads/feature/space-before-colon'
    };
    const eventPath = join(cwd, 'tmp-gh-event-space-before-colon.json');
    writeFileSync(eventPath, JSON.stringify(event), 'utf8');

    const env = {
      ...process.env,
      GITHUB_TOKEN: 'test-token',
      GITHUB_REPOSITORY: 'owner/repo',
      GITHUB_EVENT_NAME: 'pull_request',
      GITHUB_EVENT_PATH: eventPath,
      AE_COVERAGE_DRY_RUN: '1'
    } as NodeJS.ProcessEnv;

    const res = spawnSync('node', ['scripts/coverage/pr-coverage-summary.mjs'], { cwd, env, encoding: 'utf8' });
    expect(res.status).toBe(0);
    const out = res.stdout || '';
    expect(out).toContain('Threshold (effective): 85%');
    expect(out).toContain('- via label: coverage :85');
  });

  it('accepts case-insensitive label with space and percent (COVERAGE : 90 %)', () => {
    const cwd = process.cwd();
    const covDir = join(cwd, 'coverage');
    try { mkdirSync(covDir, { recursive: true }); } catch {}
    const covPath = join(covDir, 'coverage-summary.json');
    writeFileSync(covPath, JSON.stringify({ total: { lines: { pct: 95 } } }), 'utf8');

    const event = {
      pull_request: { number: 165, labels: [ { name: 'COVERAGE : 90 %' } ] },
      ref: 'refs/heads/feature/space-and-percent'
    };
    const eventPath = join(cwd, 'tmp-gh-event-space-and-percent.json');
    writeFileSync(eventPath, JSON.stringify(event), 'utf8');

    const env = {
      ...process.env,
      GITHUB_TOKEN: 'test-token',
      GITHUB_REPOSITORY: 'owner/repo',
      GITHUB_EVENT_NAME: 'pull_request',
      GITHUB_EVENT_PATH: eventPath,
      AE_COVERAGE_DRY_RUN: '1'
    } as NodeJS.ProcessEnv;

    const res = spawnSync('node', ['scripts/coverage/pr-coverage-summary.mjs'], { cwd, env, encoding: 'utf8' });
    expect(res.status).toBe(0);
    const out = res.stdout || '';
    expect(out).toContain('Threshold (effective): 90%');
    expect(out).toContain('- via label: COVERAGE : 90 %');
  });

  it('enforce-coverage with invalid label uses repo var and is [blocking]', () => {
    const cwd = process.cwd();
    const covDir = join(cwd, 'coverage');
    try { mkdirSync(covDir, { recursive: true }); } catch {}
    const covPath = join(covDir, 'coverage-summary.json');
    writeFileSync(covPath, JSON.stringify({ total: { lines: { pct: 88 } } }), 'utf8');

    const event = {
      pull_request: { number: 166, labels: [ { name: 'coverage:abc' }, { name: 'enforce-coverage' } ] },
      ref: 'refs/heads/feature/enforce-invalid-label'
    };
    const eventPath = join(cwd, 'tmp-gh-event-enforce-invalid-label.json');
    writeFileSync(eventPath, JSON.stringify(event), 'utf8');

    const env = {
      ...process.env,
      GITHUB_TOKEN: 'test-token',
      GITHUB_REPOSITORY: 'owner/repo',
      GITHUB_EVENT_NAME: 'pull_request',
      GITHUB_EVENT_PATH: eventPath,
      AE_COVERAGE_DRY_RUN: '1',
      COVERAGE_DEFAULT_THRESHOLD: '84'
    } as NodeJS.ProcessEnv;

    const res = spawnSync('node', ['scripts/coverage/pr-coverage-summary.mjs'], { cwd, env, encoding: 'utf8' });
    expect(res.status).toBe(0);
    const out = res.stdout || '';
    expect(out).toContain('- via label: coverage:abc (invalid, ignored)');
    expect(out).toContain('Threshold (effective): 84%');
    expect(out).toContain('Source: repo var');
    expect(out).toMatch(/\[blocking\]/);
    expect(out).toContain('Policy source: enforced via label: enforce-coverage');
  });

  it('Gate OK when coverage equals threshold (>= comparator)', () => {
    const cwd = process.cwd();
    const covDir = join(cwd, 'coverage');
    try { mkdirSync(covDir, { recursive: true }); } catch {}
    const covPath = join(covDir, 'coverage-summary.json');
    writeFileSync(covPath, JSON.stringify({ total: { lines: { pct: 80 } } }), 'utf8');

    const event = {
      pull_request: { number: 167, labels: [ { name: 'coverage:80' } ] },
      ref: 'refs/heads/feature/equals-threshold'
    };
    const eventPath = join(cwd, 'tmp-gh-event-equals-threshold.json');
    writeFileSync(eventPath, JSON.stringify(event), 'utf8');

    const env = {
      ...process.env,
      GITHUB_TOKEN: 'test-token',
      GITHUB_REPOSITORY: 'owner/repo',
      GITHUB_EVENT_NAME: 'pull_request',
      GITHUB_EVENT_PATH: eventPath,
      AE_COVERAGE_DRY_RUN: '1'
    } as NodeJS.ProcessEnv;

    const res = spawnSync('node', ['scripts/coverage/pr-coverage-summary.mjs'], { cwd, env, encoding: 'utf8' });
    expect(res.status).toBe(0);
    const out = res.stdout || '';
    expect(out).toMatch(/Gate: OK \(80% >= 80%\)/);
  });

  it('accepts boundary label value 0', () => {
    const cwd = process.cwd();
    const covDir = join(cwd, 'coverage');
    try { mkdirSync(covDir, { recursive: true }); } catch {}
    const covPath = join(covDir, 'coverage-summary.json');
    writeFileSync(covPath, JSON.stringify({ total: { lines: { pct: 5 } } }), 'utf8');

    const event = {
      pull_request: { number: 143, labels: [ { name: 'coverage:0' } ] },
      ref: 'refs/heads/feature/boundary0'
    };
    const eventPath = join(cwd, 'tmp-gh-event-boundary0.json');
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
    expect(out).toContain('Threshold (effective): 0%');
    expect(out).toContain('- via label: coverage:0');
  });

  it('accepts boundary label value 100', () => {
    const cwd = process.cwd();
    const covDir = join(cwd, 'coverage');
    try { mkdirSync(covDir, { recursive: true }); } catch {}
    const covPath = join(covDir, 'coverage-summary.json');
    writeFileSync(covPath, JSON.stringify({ total: { lines: { pct: 100 } } }), 'utf8');

    const event = {
      pull_request: { number: 144, labels: [ { name: 'coverage:100' } ] },
      ref: 'refs/heads/feature/boundary100'
    };
    const eventPath = join(cwd, 'tmp-gh-event-boundary100.json');
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
    expect(out).toContain('Threshold (effective): 100%');
    expect(out).toContain('- via label: coverage:100');
  });

  it('prints summary in dry-run when GITHUB_REPOSITORY is missing (fallback to event payload)', () => {
    const cwd = process.cwd();
    const covDir = join(cwd, 'coverage');
    try { mkdirSync(covDir, { recursive: true }); } catch {}
    const covPath = join(covDir, 'coverage-summary.json');
    writeFileSync(covPath, JSON.stringify({ total: { lines: { pct: 80 } } }), 'utf8');

    const event = {
      repository: { full_name: 'owner/repo' },
      pull_request: { number: 140, labels: [] },
      ref: 'refs/heads/feature/repo-fallback'
    };
    const eventPath = join(cwd, 'tmp-gh-event-norepo.json');
    writeFileSync(eventPath, JSON.stringify(event), 'utf8');

    const env = {
      ...process.env,
      GITHUB_TOKEN: 'test-token',
      GITHUB_REPOSITORY: '',
      GITHUB_EVENT_NAME: 'pull_request',
      GITHUB_EVENT_PATH: eventPath,
      AE_COVERAGE_DRY_RUN: '1',
      COVERAGE_DEFAULT_THRESHOLD: '80'
    } as NodeJS.ProcessEnv;

    const res = spawnSync('node', ['scripts/coverage/pr-coverage-summary.mjs'], { cwd, env, encoding: 'utf8' });
    expect(res.status).toBe(0);
    const out = res.stdout || '';
    expect(out).toContain('AE-COVERAGE-SUMMARY (dry-run)');
    expect(out).toContain('Coverage (lines): 80%');
  });

  it('dry-run prints body even without GITHUB_TOKEN', () => {
    const cwd = process.cwd();
    const covDir = join(cwd, 'coverage');
    try { mkdirSync(covDir, { recursive: true }); } catch {}
    const covPath = join(covDir, 'coverage-summary.json');
    writeFileSync(covPath, JSON.stringify({ total: { lines: { pct: 80 } } }), 'utf8');

    const event = {
      repository: { full_name: 'owner/repo' },
      pull_request: { number: 141, labels: [] }
    };
    const eventPath = join(cwd, 'tmp-gh-event-dry-notoken.json');
    writeFileSync(eventPath, JSON.stringify(event), 'utf8');

    const env = {
      ...process.env,
      GITHUB_TOKEN: '',
      GITHUB_REPOSITORY: 'owner/repo',
      GITHUB_EVENT_NAME: 'pull_request',
      GITHUB_EVENT_PATH: eventPath,
      AE_COVERAGE_DRY_RUN: '1'
    } as NodeJS.ProcessEnv;

    const res = spawnSync('node', ['scripts/coverage/pr-coverage-summary.mjs'], { cwd, env, encoding: 'utf8' });
    expect(res.status).toBe(0);
    const out = res.stdout || '';
    expect(out).toContain('AE-COVERAGE-SUMMARY (dry-run)');
    expect(out).toContain('Coverage (lines): 80%');
  });

  it('skips posting when AE_COVERAGE_SKIP_COMMENT=1', () => {
    const cwd = process.cwd();
    const env = {
      ...process.env,
      AE_COVERAGE_SKIP_COMMENT: '1'
    } as NodeJS.ProcessEnv;
    const res = spawnSync('node', ['scripts/coverage/pr-coverage-summary.mjs'], { cwd, env, encoding: 'utf8' });
    expect(res.status).toBe(0);
    const out = res.stdout || '';
    expect(out).toContain('AE_COVERAGE_SKIP_COMMENT');
  });

  it('skips upsert gracefully when repository coordinates cannot be resolved', () => {
    const cwd = process.cwd();
    const covDir = join(cwd, 'coverage');
    try { mkdirSync(covDir, { recursive: true }); } catch {}
    const covPath = join(covDir, 'coverage-summary.json');
    writeFileSync(covPath, JSON.stringify({ total: { lines: { pct: 80 } } }), 'utf8');

    const event = {
      // No repository object and no full_name fallback
      pull_request: { number: 141, labels: [] }
    };
    const eventPath = join(cwd, 'tmp-gh-event-no-repo.json');
    writeFileSync(eventPath, JSON.stringify(event), 'utf8');

    const env = {
      ...process.env,
      GITHUB_TOKEN: 'test-token',
      GITHUB_REPOSITORY: '',
      GITHUB_EVENT_NAME: 'pull_request',
      GITHUB_EVENT_PATH: eventPath,
      // Intentionally not setting AE_COVERAGE_DRY_RUN to hit the skip path before posting
      COVERAGE_DEFAULT_THRESHOLD: '80'
    } as NodeJS.ProcessEnv;

    const res = spawnSync('node', ['scripts/coverage/pr-coverage-summary.mjs'], { cwd, env, encoding: 'utf8' });
    expect(res.status).toBe(0);
    const out = res.stdout || '';
    expect(out).toContain('unable to resolve repository coordinates');
  });

  it('skips when no event payload is provided', () => {
    const cwd = process.cwd();
    const env = {
      ...process.env,
      GITHUB_TOKEN: 'test-token',
      GITHUB_REPOSITORY: 'owner/repo',
      GITHUB_EVENT_NAME: 'pull_request',
      GITHUB_EVENT_PATH: '',
      AE_COVERAGE_DRY_RUN: ''
    } as NodeJS.ProcessEnv;

    const res = spawnSync('node', ['scripts/coverage/pr-coverage-summary.mjs'], { cwd, env, encoding: 'utf8' });
    expect(res.status).toBe(0);
    const out = res.stdout || '';
    expect(out).toContain('No event payload; skipping PR comment');
  });

  it('skips when event payload JSON is malformed', () => {
    const cwd = process.cwd();
    const eventPath = join(cwd, 'tmp-gh-event-malformed.json');
    // Write malformed JSON
    writeFileSync(eventPath, '{ pull_request: ', 'utf8');

    const env = {
      ...process.env,
      GITHUB_TOKEN: 'test-token',
      GITHUB_REPOSITORY: 'owner/repo',
      GITHUB_EVENT_NAME: 'pull_request',
      GITHUB_EVENT_PATH: eventPath,
      AE_COVERAGE_DRY_RUN: ''
    } as NodeJS.ProcessEnv;

    const res = spawnSync('node', ['scripts/coverage/pr-coverage-summary.mjs'], { cwd, env, encoding: 'utf8' });
    expect(res.status).toBe(0);
    const out = res.stdout || '';
    expect(out).toContain('Warning: failed to parse event payload; skipping PR comment');
  });

  it('shows [blocking] with main push when COVERAGE_ENFORCE_MAIN=1', () => {
    const cwd = process.cwd();
    const covDir = join(cwd, 'coverage');
    try { mkdirSync(covDir, { recursive: true }); } catch {}
    const covPath = join(covDir, 'coverage-summary.json');
    writeFileSync(covPath, JSON.stringify({ total: { lines: { pct: 82 } } }), 'utf8');

    const event = {
      repository: { full_name: 'owner/repo' },
      // Simulate push event on main
      ref: 'refs/heads/main'
    };
    const eventPath = join(cwd, 'tmp-gh-event-main.json');
    writeFileSync(eventPath, JSON.stringify(event), 'utf8');

    const env = {
      ...process.env,
      GITHUB_TOKEN: 'test-token',
      GITHUB_REPOSITORY: '',
      GITHUB_EVENT_NAME: 'push',
      GITHUB_EVENT_PATH: eventPath,
      AE_COVERAGE_DRY_RUN: '1',
      COVERAGE_DEFAULT_THRESHOLD: '80',
      COVERAGE_ENFORCE_MAIN: '1'
    } as NodeJS.ProcessEnv;

    const res = spawnSync('node', ['scripts/coverage/pr-coverage-summary.mjs'], { cwd, env, encoding: 'utf8' });
    expect(res.status).toBe(0);
    const out = res.stdout || '';
    expect(out).toMatch(/\[blocking\]/);
    expect(out).toContain('Policy: enforced');
    expect(out).toContain('Policy source: enforced via main + repo vars (COVERAGE_ENFORCE_MAIN)');
  });

  it('label override wins over repo var value', () => {
    const cwd = process.cwd();
    const covDir = join(cwd, 'coverage');
    try { mkdirSync(covDir, { recursive: true }); } catch {}
    const covPath = join(covDir, 'coverage-summary.json');
    writeFileSync(covPath, JSON.stringify({ total: { lines: { pct: 88 } } }), 'utf8');

    const event = {
      pull_request: { number: 136, labels: [ { name: 'coverage:85' } ] },
      ref: 'refs/heads/feature/override'
    };
    const eventPath = join(cwd, 'tmp-gh-event-override.json');
    writeFileSync(eventPath, JSON.stringify(event), 'utf8');

    const env = {
      ...process.env,
      GITHUB_TOKEN: 'test-token',
      GITHUB_REPOSITORY: 'owner/repo',
      GITHUB_EVENT_NAME: 'pull_request',
      GITHUB_EVENT_PATH: eventPath,
      AE_COVERAGE_DRY_RUN: '1',
      COVERAGE_DEFAULT_THRESHOLD: '90'
    } as NodeJS.ProcessEnv;

    const res = spawnSync('node', ['scripts/coverage/pr-coverage-summary.mjs'], { cwd, env, encoding: 'utf8' });
    expect(res.status).toBe(0);
    const out = res.stdout || '';
    // Effective threshold from label, despite repo var being higher
    expect(out).toContain('Threshold (effective): 85%');
    expect(out).toContain('- via label: coverage:85');
    expect(out).toContain('- repo var: COVERAGE_DEFAULT_THRESHOLD=90%');
    expect(out).toMatch(/Gate: OK \(88% >= 85%\)/);
  });

  it('shows [blocking] mode when enforce-coverage label is present', () => {
    const cwd = process.cwd();
    const covDir = join(cwd, 'coverage');
    try { mkdirSync(covDir, { recursive: true }); } catch {}
    const covPath = join(covDir, 'coverage-summary.json');
    writeFileSync(covPath, JSON.stringify({ total: { lines: { pct: 81 } } }), 'utf8');

    const event = {
      pull_request: { number: 134, labels: [ { name: 'enforce-coverage' } ] },
      ref: 'refs/heads/feature/blocking'
    };
    const eventPath = join(cwd, 'tmp-gh-event-blocking.json');
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
    expect(out).toMatch(/Gate: OK \(81% >= 80%\) \[blocking\]/);
    expect(out).toContain('Policy: enforced');
    expect(out).toContain('Policy source: enforced via label: enforce-coverage');
  });

  it('accepts case-insensitive enforce-coverage label for blocking mode', () => {
    const cwd = process.cwd();
    const covDir = join(cwd, 'coverage');
    try { mkdirSync(covDir, { recursive: true }); } catch {}
    const covPath = join(covDir, 'coverage-summary.json');
    writeFileSync(covPath, JSON.stringify({ total: { lines: { pct: 81 } } }), 'utf8');

    const event = {
      pull_request: { number: 137, labels: [ { name: 'EnFoRcE-CoVeRaGe' } ] },
      ref: 'refs/heads/feature/blocking-ci'
    };
    const eventPath = join(cwd, 'tmp-gh-event-blocking-ci.json');
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
    expect(out).toMatch(/\[blocking\]/);
    expect(out).toContain('Policy: enforced');
    expect(out).toContain('Policy source: enforced via label: enforce-coverage');
  });

  it('uses label threshold and [blocking] when both coverage:<pct> and enforce-coverage are present', () => {
    const cwd = process.cwd();
    const covDir = join(cwd, 'coverage');
    try { mkdirSync(covDir, { recursive: true }); } catch {}
    const covPath = join(covDir, 'coverage-summary.json');
    writeFileSync(covPath, JSON.stringify({ total: { lines: { pct: 86 } } }), 'utf8');

    const event = {
      pull_request: { number: 153, labels: [ { name: 'coverage:85' }, { name: 'enforce-coverage' } ] },
      ref: 'refs/heads/feature/label-plus-enforce'
    };
    const eventPath = join(cwd, 'tmp-gh-event-label-plus-enforce.json');
    writeFileSync(eventPath, JSON.stringify(event), 'utf8');

    const env = {
      ...process.env,
      GITHUB_TOKEN: 'test-token',
      GITHUB_REPOSITORY: 'owner/repo',
      GITHUB_EVENT_NAME: 'pull_request',
      GITHUB_EVENT_PATH: eventPath,
      AE_COVERAGE_DRY_RUN: '1',
      COVERAGE_DEFAULT_THRESHOLD: '90'
    } as NodeJS.ProcessEnv;

    const res = spawnSync('node', ['scripts/coverage/pr-coverage-summary.mjs'], { cwd, env, encoding: 'utf8' });
    expect(res.status).toBe(0);
    const out = res.stdout || '';
    expect(out).toContain('Threshold (effective): 85%');
    expect(out).toMatch(/\[blocking\]/);
    expect(out).toContain('Policy source: enforced via label: enforce-coverage');
  });

  it('handles space after colon in coverage label (e.g., coverage: 85)', () => {
    const cwd = process.cwd();
    const covDir = join(cwd, 'coverage');
    try { mkdirSync(covDir, { recursive: true }); } catch {}
    const covPath = join(covDir, 'coverage-summary.json');
    writeFileSync(covPath, JSON.stringify({ total: { lines: { pct: 90 } } }), 'utf8');

    const event = {
      pull_request: { number: 131, labels: [ { name: 'coverage: 85' } ] },
      ref: 'refs/heads/feature/space'
    };
    const eventPath = join(cwd, 'tmp-gh-event-space.json');
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
    expect(out).toContain('Threshold (effective): 85%');
    expect(out).toContain('- via label: coverage: 85');
  });
});
