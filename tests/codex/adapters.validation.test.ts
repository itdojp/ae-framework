import { describe, it, expect } from 'vitest';
import { validateAdapterJson } from '../../scripts/codex/ae-playbook.mjs';

describe('Adapters validation (warn-only minimal schema)', () => {
  it('lighthouse minimal passes', () => {
    const rel = 'artifacts/lighthouse/summary.json';
    const j = { adapter: 'lighthouse', status: 'warn', summary: 'Lighthouse: Perf 78, A11y 95' };
    const warns = validateAdapterJson(rel, j);
    expect(Array.isArray(warns)).toBe(true);
    // summary exists, performance hint present ⇒ no warnings specific to lh
    expect(warns.find(w => /lighthouse/.test(w.message || ''))).toBeUndefined();
  });

  it('axe minimal passes', () => {
    const rel = 'artifacts/adapters/axe/summary.json';
    const j = { adapter: 'axe', status: 'ok', summary: 'AXE a11y violations: 0' };
    const warns = validateAdapterJson(rel, j);
    expect(warns.find(w => /axe/.test(w.message || ''))).toBeUndefined();
  });

  it('jest minimal passes', () => {
    const rel = 'artifacts/adapters/jest/summary.json';
    const j = { adapter: 'jest', status: 'ok', summary: 'Jest: 20 passed / 0 failed' };
    const warns = validateAdapterJson(rel, j);
    expect(warns.find(w => /jest/.test(w.message || ''))).toBeUndefined();
  });

  it('vitest minimal passes', () => {
    const rel = 'artifacts/adapters/vitest/summary.json';
    const j = { adapter: 'vitest', status: 'ok', summary: 'Vitest: 10 tests passed' };
    const warns = validateAdapterJson(rel, j);
    expect(warns.find(w => /vitest/.test(w.message || ''))).toBeUndefined();
  });

  it('warns on missing summary', () => {
    const rel = 'artifacts/adapters/jest/summary.json';
    const j = { adapter: 'jest', status: 'ok' } as any;
    const warns = validateAdapterJson(rel, j);
    expect(warns.some(w => /missing summary/.test(w.message || ''))).toBe(true);
  });

  it('warns on invalid status', () => {
    const rel = 'artifacts/adapters/lighthouse/summary.json';
    const j = { adapter: 'lighthouse', status: 'ALERT', summary: 'Lighthouse Perf 75' } as any;
    const warns = validateAdapterJson(rel, j);
    expect(warns.some(w => /invalid status/i.test(w.message || ''))).toBe(true);
  });
});

