import type { AeConfig } from '../core/config.js';
import { getQualityGate } from './quality-policy-loader.js';

export type CoverageThresholds = { branches: number; lines: number; functions: number; statements: number };

export async function resolveCoverageThresholds(cfg: AeConfig, envProfile: string): Promise<{
  effective: CoverageThresholds;
  hint: CoverageThresholds | null;
  mismatch: boolean;
}> {
  const hint = cfg?.qa?.coverageThreshold ?? null;
  try {
    const gate = getQualityGate('coverage', envProfile);
    const eff: CoverageThresholds = {
      lines: Number(gate.thresholds.lines ?? 80),
      functions: Number(gate.thresholds.functions ?? 80),
      branches: Number(gate.thresholds.branches ?? 80),
      statements: Number(gate.thresholds.statements ?? 80),
    };
    const mismatch = hint ? (
      hint.lines !== eff.lines ||
      hint.functions !== eff.functions ||
      hint.branches !== eff.branches ||
      hint.statements !== eff.statements
    ) : false;
    return { effective: eff, hint, mismatch };
  } catch (e) {
    if (hint) {
      return { effective: hint, hint, mismatch: false };
    }
    const eff: CoverageThresholds = { lines: 80, functions: 80, branches: 80, statements: 80 };
    return { effective: eff, hint: null, mismatch: false };
  }
}

