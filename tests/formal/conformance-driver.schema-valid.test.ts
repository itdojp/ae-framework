import { describe, it, expect } from 'vitest';
import { execSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import { createTempDir, writeTempJson, rmrf } from '../_helpers/tmpfs.js';

describe('Formal: conformance-driver emits schema-conformant summary', () => {
  it('writes conformance-summary.json with required ran/ok fields', () => {
    const tmpDir = createTempDir('conformance-driver-');
    try {
      const replay = {
        traceId: 't-1',
        totalEvents: 3,
        violatedInvariants: []
      };
      const tracePath = writeTempJson(tmpDir, 'replay.summary.json', replay);
      const specPath = writeTempJson(tmpDir, 'tla-summary.json', { result: 'ok' });
      const hooksPath = writeTempJson(tmpDir, 'hooks.json', []);
      const out = path.join(tmpDir, 'conformance-summary.json');

      execSync('node scripts/formal/conformance-driver.mjs', {
        stdio: 'inherit',
        env: {
          ...process.env,
          CONFORMANCE_TRACE: tracePath,
          CONFORMANCE_SPEC: specPath,
          CONFORMANCE_RUNTIME_HOOKS: hooksPath,
          CONFORMANCE_OUTPUT: out
        }
      });
      expect(fs.existsSync(out)).toBe(true);

      const j = JSON.parse(fs.readFileSync(out, 'utf-8'));
      expect(typeof j.ran).toBe('boolean');
      expect(j.ok === true || j.ok === false || j.ok === null).toBe(true);
      expect(j.tool).toBe('conformance-driver');
    } finally {
      rmrf(tmpDir);
    }
  });
});
