import { describe, expect, it } from 'vitest';
import {
  EXPLICIT_EMPTY_SENTINEL,
  resolveAutomationConfig,
  toGithubEnv,
} from '../../../scripts/ci/lib/automation-config.mjs';

describe('automation-config', () => {
  it('uses defaults when profile and variables are not set', () => {
    const config = resolveAutomationConfig({});
    expect(config.profile.resolved).toBe('');
    expect(config.values.AE_AUTOMATION_GLOBAL_DISABLE).toBe('0');
    expect(config.values.AE_COPILOT_AUTO_FIX).toBe('0');
    expect(config.values.AE_AUTO_MERGE).toBe('0');
    expect(config.values.AE_COPILOT_AUTO_FIX_SCOPE).toBe('docs');
    expect(config.values.AE_AUTO_MERGE_MODE).toBe('all');
    expect(config.values.AE_AUTO_MERGE_REQUIRE_RISK_LOW).toBe('1');
    expect(config.values.AE_AUTO_MERGE_REQUIRE_CHANGE_PACKAGE).toBe('1');
    expect(config.values.AE_AUTO_MERGE_CHANGE_PACKAGE_ALLOW_WARN).toBe('1');
    expect(config.values.AE_GH_RETRY_MULTIPLIER).toBe('2');
    expect(config.values.AE_GH_RETRY_JITTER_MS).toBe('250');
    expect(config.warnings).toEqual([]);
  });

  it('loads balanced profile values', () => {
    const config = resolveAutomationConfig({
      AE_AUTOMATION_PROFILE: 'balanced',
    });
    expect(config.profile.resolved).toBe('balanced');
    expect(config.values.AE_AUTOMATION_GLOBAL_DISABLE).toBe('0');
    expect(config.values.AE_COPILOT_AUTO_FIX).toBe('1');
    expect(config.values.AE_COPILOT_AUTO_FIX_SCOPE).toBe('docs');
    expect(config.values.AE_AUTO_MERGE).toBe('1');
    expect(config.values.AE_AUTO_MERGE_MODE).toBe('label');
    expect(config.values.AE_AUTO_MERGE_LABEL).toBe('auto-merge');
    expect(config.values.AE_AUTO_MERGE_REQUIRE_RISK_LOW).toBe('1');
    expect(config.values.AE_AUTO_MERGE_REQUIRE_CHANGE_PACKAGE).toBe('1');
    expect(config.values.AE_AUTO_MERGE_CHANGE_PACKAGE_ALLOW_WARN).toBe('1');
    expect(config.values.AE_GH_RETRY_MULTIPLIER).toBe('2');
    expect(config.values.AE_GH_RETRY_JITTER_MS).toBe('250');
  });

  it('prefers explicit values over profile values', () => {
    const config = resolveAutomationConfig({
      AE_AUTOMATION_PROFILE: 'aggressive',
      AE_COPILOT_AUTO_FIX_SCOPE: 'docs',
      AE_AUTO_MERGE_MODE: 'label',
      AE_AUTO_MERGE_LABEL: 'manual-opt-in',
    });
    expect(config.values.AE_COPILOT_AUTO_FIX_SCOPE).toBe('docs');
    expect(config.sources.AE_COPILOT_AUTO_FIX_SCOPE).toBe('explicit');
    expect(config.values.AE_AUTO_MERGE_MODE).toBe('label');
    expect(config.values.AE_AUTO_MERGE_LABEL).toBe('manual-opt-in');
    expect(config.values.AE_AUTO_MERGE_REQUIRE_RISK_LOW).toBe('1');
  });

  it('supports explicit empty string override for string fields', () => {
    const config = resolveAutomationConfig({
      AE_AUTOMATION_PROFILE: 'conservative',
      AE_COPILOT_AUTO_FIX_LABEL: EXPLICIT_EMPTY_SENTINEL,
    });
    expect(config.values.AE_COPILOT_AUTO_FIX_LABEL).toBe('');
    expect(config.sources.AE_COPILOT_AUTO_FIX_LABEL).toBe('explicit');
  });

  it('falls back on invalid explicit values with warnings', () => {
    const config = resolveAutomationConfig({
      AE_AUTOMATION_PROFILE: 'balanced',
      AE_COPILOT_AUTO_FIX_SCOPE: 'invalid-scope',
      AE_GH_RETRY_MAX_ATTEMPTS: 'NaN',
    });
    expect(config.values.AE_COPILOT_AUTO_FIX_SCOPE).toBe('docs');
    expect(config.values.AE_GH_RETRY_MAX_ATTEMPTS).toBe('8');
    expect(config.warnings.some((w) => w.includes('AE_COPILOT_AUTO_FIX_SCOPE'))).toBe(true);
    expect(config.warnings.some((w) => w.includes('AE_GH_RETRY_MAX_ATTEMPTS'))).toBe(true);
  });

  it('warns when label mode is enabled without label', () => {
    const config = resolveAutomationConfig({
      AE_AUTO_MERGE: '1',
      AE_AUTO_MERGE_MODE: 'label',
      AE_AUTO_MERGE_LABEL: '',
    });
    expect(config.warnings.some((w) => w.includes('AE_AUTO_MERGE_MODE=label'))).toBe(true);
  });

  it('exports resolved values as GitHub env lines', () => {
    const config = resolveAutomationConfig({
      AE_AUTOMATION_PROFILE: 'conservative',
    });
    const envBody = toGithubEnv(config);
    expect(envBody).toContain('AE_AUTOMATION_PROFILE_RESOLVED=conservative');
    expect(envBody).toContain('AE_AUTOMATION_GLOBAL_DISABLE=0');
    expect(envBody).toContain('AE_COPILOT_AUTO_FIX=1');
    expect(envBody).toContain('AE_AUTO_MERGE_MODE=label');
  });

  it('normalizes global disable toggle values', () => {
    const on = resolveAutomationConfig({
      AE_AUTOMATION_GLOBAL_DISABLE: 'true',
    });
    const off = resolveAutomationConfig({
      AE_AUTOMATION_GLOBAL_DISABLE: 'no',
    });
    expect(on.values.AE_AUTOMATION_GLOBAL_DISABLE).toBe('1');
    expect(off.values.AE_AUTOMATION_GLOBAL_DISABLE).toBe('0');
  });

  it('allows overriding risk:low requirement for auto-merge', () => {
    const config = resolveAutomationConfig({
      AE_AUTO_MERGE_REQUIRE_RISK_LOW: 'false',
    });
    expect(config.values.AE_AUTO_MERGE_REQUIRE_RISK_LOW).toBe('0');
  });

  it('allows overriding change-package guard for auto-merge', () => {
    const config = resolveAutomationConfig({
      AE_AUTO_MERGE_REQUIRE_CHANGE_PACKAGE: 'false',
      AE_AUTO_MERGE_CHANGE_PACKAGE_ALLOW_WARN: 'false',
    });
    expect(config.values.AE_AUTO_MERGE_REQUIRE_CHANGE_PACKAGE).toBe('0');
    expect(config.values.AE_AUTO_MERGE_CHANGE_PACKAGE_ALLOW_WARN).toBe('0');
  });

  it('sanitizes newline characters when exporting GitHub env lines', () => {
    const config = resolveAutomationConfig({
      AE_COPILOT_AUTO_FIX_LABEL: 'copilot\nauto-fix',
    });
    const envBody = toGithubEnv(config);
    expect(envBody).toContain('AE_COPILOT_AUTO_FIX_LABEL=copilot auto-fix');
  });
});
