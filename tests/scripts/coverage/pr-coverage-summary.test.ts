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
