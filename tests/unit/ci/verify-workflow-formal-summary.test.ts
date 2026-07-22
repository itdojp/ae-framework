import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, expect, it } from 'vitest';

describe('verify workflow formal PR summary boundary', () => {
  const workflow = readFileSync(resolve('.github/workflows/verify.yml'), 'utf8');

  it('counts only recognized reports with completed checker executions', () => {
    expect(workflow).toContain('.schemaVersion == "model-check-report/v1"');
    expect(workflow).toContain('.executionStatus=="executed" and .ok==true');
    expect(workflow).toContain('node scripts/verify/enforce-model-check-report.mjs --artifact-root "$(dirname "$FILE")" "$FILE"');
    expect(workflow).toContain('node scripts/verify/enforce-model-check-report.mjs --contract-only --artifact-root artifacts/codex artifacts/codex/model-check.json');
    expect(workflow).toContain('artifacts/codex/*.tlc.log.txt');
    expect(workflow).toContain('artifacts/codex/*.alloy.log.txt');
    expect(workflow).toContain('Validate downloaded model-check log references');
    expect(workflow).toContain('no completed checker execution counted for status=%s');
    expect(workflow).toContain('unrecognized or invalid artifact; not counted as execution evidence');
    expect(workflow).not.toContain('Model Check (TLC): %s/%s (%s%%) modules ok');
  });
});
