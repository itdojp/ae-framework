import { describe, it, expect, vi, beforeEach } from 'vitest';

vi.mock('../../src/utils/quality-policy-loader.js', async () => {
  // default mock; individual tests will override via mockImplementation
  const getQualityGate = vi.fn().mockReturnValue({
    thresholds: { lines: 85, functions: 85, branches: 80, statements: 85 },
    enforcement: 'strict',
  });
  return { getQualityGate };
});

// Import after mocking to ensure the mocked module is used
import { resolveCoverageThresholds } from '../../src/commands/qa/run.js';

// Access mocked module for overriding implementations per test
import * as policyMod from '../../src/utils/quality-policy-loader.js';

describe('qa config hints vs policy thresholds', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  it('uses policy thresholds as source of truth and reports mismatch when ae.config differs', async () => {
    // Policy returns 85/85/80/85 by default per vi.mock above
    const cfg: any = {
      qa: { coverageThreshold: { lines: 90, functions: 90, branches: 90, statements: 90 } },
    };

    const { effective, hint, mismatch } = await resolveCoverageThresholds(cfg, 'ci');

    expect(effective).toEqual({ lines: 85, functions: 85, branches: 80, statements: 85 });
    expect(hint).toEqual({ lines: 90, functions: 90, branches: 90, statements: 90 });
    expect(mismatch).toBe(true);
  });

  it('does not report mismatch when ae.config matches policy thresholds', async () => {
    // Ensure policy returns specific thresholds
    (policyMod.getQualityGate as any).mockReturnValueOnce({
      thresholds: { lines: 90, functions: 90, branches: 90, statements: 90 },
      enforcement: 'strict',
    });

    const cfg: any = {
      qa: { coverageThreshold: { lines: 90, functions: 90, branches: 90, statements: 90 } },
    };

    const { effective, hint, mismatch } = await resolveCoverageThresholds(cfg, 'ci');
    expect(effective).toEqual({ lines: 90, functions: 90, branches: 90, statements: 90 });
    expect(hint).toEqual({ lines: 90, functions: 90, branches: 90, statements: 90 });
    expect(mismatch).toBe(false);
  });

  it('falls back to ae.config hint when policy fails to load', async () => {
    (policyMod.getQualityGate as any).mockImplementationOnce(() => {
      throw new Error('load error');
    });
    const cfg: any = {
      qa: { coverageThreshold: { lines: 70, functions: 70, branches: 70, statements: 70 } },
    };
    const { effective, hint, mismatch } = await resolveCoverageThresholds(cfg, 'ci');
    expect(effective).toEqual({ lines: 70, functions: 70, branches: 70, statements: 70 });
    expect(hint).toEqual({ lines: 70, functions: 70, branches: 70, statements: 70 });
    expect(mismatch).toBe(false);
  });

  it('falls back to defaults when neither policy nor ae.config thresholds are available', async () => {
    (policyMod.getQualityGate as any).mockImplementationOnce(() => {
      throw new Error('load error');
    });
    const cfg: any = { qa: {} };
    const { effective, hint, mismatch } = await resolveCoverageThresholds(cfg, 'development');
    expect(effective).toEqual({ lines: 80, functions: 80, branches: 80, statements: 80 });
    expect(hint).toBeNull();
    expect(mismatch).toBe(false);
  });
});

