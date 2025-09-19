import { describe, it, expect, beforeEach, vi } from 'vitest';
import { warnConfigThresholdHint, _resetHintWarningFlagForTests } from '../../src/utils/config-hints-logger.js';

describe('config hints logger', () => {
  const hint = { lines: 90, functions: 90, branches: 85, statements: 90 };

  beforeEach(() => {
    _resetHintWarningFlagForTests();
    vi.restoreAllMocks();
    delete process.env['AE_SUPPRESS_CONFIG_HINTS'];
  });

  it('logs only once per process (dedup)', () => {
    const spy = vi.spyOn(console, 'warn').mockImplementation(() => {});
    warnConfigThresholdHint({ hint, mismatch: true, envProfile: 'ci' });
    warnConfigThresholdHint({ hint, mismatch: false, envProfile: 'ci' });
    expect(spy.mock.calls.length).toBeGreaterThan(0);
    // First call emits multiple lines; second call emits none (deduped)
    const firstCount = spy.mock.calls.length;
    warnConfigThresholdHint({ hint, mismatch: true, envProfile: 'development' });
    expect(spy.mock.calls.length).toBe(firstCount); // no more warnings
  });

  it('suppresses all output when AE_SUPPRESS_CONFIG_HINTS=true', () => {
    process.env['AE_SUPPRESS_CONFIG_HINTS'] = 'true';
    const spy = vi.spyOn(console, 'warn').mockImplementation(() => {});
    warnConfigThresholdHint({ hint, mismatch: true, envProfile: 'ci' });
    expect(spy).not.toHaveBeenCalled();
  });
});

