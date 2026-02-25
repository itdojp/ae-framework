import { describe, expect, it } from 'vitest';
import { spawnSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import { createTempDir, rmrf } from '../_helpers/tmpfs.js';

describe('Integration: property-harness', () => {
  it('writes reproducible summary keys', () => {
    const tmpDir = createTempDir('property-harness-');
    try {
      const output = path.join(tmpDir, 'property.summary.json');
      const res = spawnSync(
        'node',
        ['scripts/testing/property-harness.mjs', '--seed=1234', '--runs=8', '--focus=trace-prop-1', `--output=${output}`],
        { encoding: 'utf-8' }
      );
      expect(res.status).toBe(0);
      expect(fs.existsSync(output)).toBe(true);
      const summary = JSON.parse(fs.readFileSync(output, 'utf-8'));
      expect(summary.seed).toBe(1234);
      expect(summary.traceId).toBe('trace-prop-1');
      expect(summary.runs).toBe(8);
      expect(typeof summary.passed).toBe('boolean');
      expect(typeof summary.failed).toBe('number');
      expect(typeof summary.durationMs).toBe('number');
      expect(typeof summary.reproducibleCommand).toBe('string');
    } finally {
      rmrf(tmpDir);
    }
  });
});
