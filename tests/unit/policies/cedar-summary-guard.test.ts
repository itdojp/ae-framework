import fs from 'node:fs';
import path from 'node:path';
import { afterEach, beforeEach, describe, expect, it } from 'vitest';

import {
  cedarSummaryCounts,
  enforceCedarSummary,
  readCedarSummary,
  writeGithubOutput,
} from '../../../scripts/policies/cedar-summary-guard.mjs';

let tmpDir: string;

beforeEach(() => {
  tmpDir = fs.mkdtempSync(path.join(process.cwd(), 'artifacts', 'tmp-cedar-summary-guard-'));
});

afterEach(() => {
  fs.rmSync(tmpDir, { recursive: true, force: true });
});

function writeSummary(summary: unknown) {
  const file = path.join(tmpDir, 'cedar-summary.json');
  fs.writeFileSync(file, JSON.stringify(summary), 'utf8');
  return file;
}

describe('cedar-summary-guard', () => {
  it('reads and exports validated integer counts only', () => {
    const summaryPath = writeSummary({
      filesScanned: 2,
      okCount: 1,
      ngCount: 1,
    });
    const outputPath = path.join(tmpDir, 'github-output.txt');
    const counts = cedarSummaryCounts(readCedarSummary(summaryPath));

    writeGithubOutput(counts, outputPath);

    expect(counts).toEqual({ files: 2, ok: 1, ng: 1 });
    expect(fs.readFileSync(outputPath, 'utf8')).toBe('files=2\nok=1\nng=1\n');
  });

  it('rejects shell-like strings instead of forwarding them as outputs', () => {
    const summaryPath = writeSummary({
      filesScanned: 1,
      okCount: 0,
      ngCount: '0; echo injected',
    });

    expect(() => cedarSummaryCounts(readCedarSummary(summaryPath))).toThrow(/ngCount must be a non-negative safe integer/);
  });

  it('enforces ngCount with the checked-in script logic', () => {
    expect(enforceCedarSummary({ filesScanned: 1, okCount: 1, ngCount: 0 })).toEqual({ files: 1, ok: 1, ng: 0 });
    expect(() => enforceCedarSummary({ filesScanned: 1, okCount: 0, ngCount: 1 })).toThrow(
      /Cedar validation found NG=1/,
    );
  });
});
