import { describe, expect, it } from 'vitest';
import { spawnSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import { createTempDir, rmrf } from '../_helpers/tmpfs.js';

describe('Integration: mbt summary', () => {
  it('writes reproducibility keys in MBT summary', () => {
    const tmpDir = createTempDir('mbt-summary-');
    try {
      const output = path.join(tmpDir, 'mbt.summary.json');
      const res = spawnSync(
        'node',
        [
          'tests/mbt/run.js',
          '--seed=42',
          '--runs=5',
          '--depth=4',
          '--trace-id=mbt-42',
          `--output=${output}`,
        ],
        { encoding: 'utf-8' }
      );
      expect(res.status).toBe(0);
      expect(fs.existsSync(output)).toBe(true);
      const summary = JSON.parse(fs.readFileSync(output, 'utf-8'));
      expect(summary.traceId).toBe('mbt-42');
      expect(summary.seed).toBe(42);
      expect(summary.runs).toBe(5);
      expect(typeof summary.passed).toBe('number');
      expect(typeof summary.failed).toBe('number');
      expect(typeof summary.durationMs).toBe('number');
      expect(typeof summary.reproducibleCommand).toBe('string');
    } finally {
      rmrf(tmpDir);
    }
  });
});
