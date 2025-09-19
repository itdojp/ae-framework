let warnedOnce = false;

export interface HintThresholds { lines: number; functions: number; branches: number; statements: number }

export function warnConfigThresholdHint(opts: {
  hint: HintThresholds;
  mismatch: boolean;
  envProfile: string;
}): { suppressed: boolean; deduped: boolean } {
  const suppress = process.env['AE_SUPPRESS_CONFIG_HINTS'];
  const suppressed = suppress === 'true' || suppress === '1';
  if (suppressed) return { suppressed: true, deduped: false };
  if (warnedOnce) return { suppressed: false, deduped: true };

  const { hint, mismatch, envProfile } = opts;
  // Single Source of Truth and precedence
  console.warn('[ae:qa] WARN: ae.config.qa.coverageThreshold is treated as a hint. Policy is the source of truth.');
  console.warn(`[ae:qa] Precedence: policy > AE-IR > ae.config (profile: ${envProfile})`);
  console.warn(`[ae:qa] hint → lines=${hint.lines}, functions=${hint.functions}, branches=${hint.branches}, statements=${hint.statements}`);
  if (mismatch) {
    console.warn('[ae:qa] HINT differs from policy thresholds. Enforcement will follow policy.');
  }
  console.warn('[ae:qa] Migrate thresholds in policy/quality.json (coverage.thresholds.*) to change enforcement.');

  warnedOnce = true;
  return { suppressed: false, deduped: false };
}

export function _resetHintWarningFlagForTests() {
  warnedOnce = false;
}

