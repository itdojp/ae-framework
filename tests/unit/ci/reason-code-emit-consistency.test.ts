import fs from 'node:fs';
import { describe, expect, it } from 'vitest';
import yaml from 'yaml';
import { resolveAutomationReasonCode } from '../../../scripts/ci/lib/automation-reason-codes.mjs';
import { resolveReasonCode as resolveAutopilotReasonCode } from '../../../scripts/ci/lib/pr-orchestration-contracts.mjs';
import {
  AUTOMATION_REPORT_SAMPLES,
  AUTOPILOT_REASON_SAMPLES,
} from '../../../scripts/ci/validate-reason-codes.mjs';

function loadRegistryCodes() {
  const parsed = yaml.parse(fs.readFileSync('policy/reason-codes.yml', 'utf8')) as {
    codes?: Array<{ code?: string }>;
  };
  return new Set(
    (parsed.codes ?? [])
      .map((entry) => String(entry?.code ?? '').trim())
      .filter(Boolean),
  );
}

describe('reason-code emit consistency', () => {
  it('autopilot reason code mappings are registered', () => {
    const registryCodes = loadRegistryCodes();
    for (const reason of AUTOPILOT_REASON_SAMPLES) {
      const code = resolveAutopilotReasonCode(reason);
      expect(code).not.toBe('');
      expect(registryCodes.has(code)).toBe(true);
    }
  });

  it('automation report reason code mappings are registered', () => {
    const registryCodes = loadRegistryCodes();
    for (const input of AUTOMATION_REPORT_SAMPLES) {
      const code = resolveAutomationReasonCode(input);
      expect(code).not.toBe('');
      expect(registryCodes.has(code)).toBe(true);
    }
  });
});
