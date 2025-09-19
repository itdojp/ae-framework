import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import * as fs from 'node:fs';
import * as path from 'node:path';
import os from 'node:os';
import { QualityGateRunner } from '../../src/quality/quality-gate-runner.js';

function tmpdir(): string {
  const d = fs.mkdtempSync(path.join(os.tmpdir(), 'ae-qgr-'));
  return d;
}

const SNAP = { ...process.env };

describe('QualityGateRunner saveReport meta injection', () => {
  beforeEach(() => { process.env = { ...SNAP }; });
  afterEach(() => { process.env = { ...SNAP }; });

  it('writes meta top-level without breaking structure', async () => {
    const runner = new QualityGateRunner();
    const out = tmpdir();
    const report = {
      timestamp: new Date().toISOString(),
      environment: 'testing',
      overallScore: 100,
      totalGates: 1,
      passedGates: 1,
      failedGates: 0,
      results: [],
      summary: { byCategory: {}, executionTime: 1, blockers: [] },
    };
    await (runner as any).saveReport(report, out);
    const files = fs.readdirSync(out).filter(f => f.endsWith('.json'));
    expect(files.length).toBeGreaterThan(0);
    const payload = JSON.parse(fs.readFileSync(path.join(out, files[0]), 'utf8'));
    expect(payload).toHaveProperty('meta');
    expect(payload.meta).toHaveProperty('agent');
    expect(payload).toHaveProperty('environment', 'testing');
    expect(payload).toHaveProperty('summary');
  });
});

