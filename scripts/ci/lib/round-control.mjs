import { sleep } from './timing.mjs';

export function readIntEnv(name, fallback, min = 0) {
  const parsed = Number.parseInt(String(process.env[name] || '').trim(), 10);
  if (!Number.isFinite(parsed)) return fallback;
  if (parsed < min) return fallback;
  return parsed;
}

export function resolveRoundWaitMs({
  round,
  baseSeconds,
  strategy = 'fixed',
  maxSeconds = baseSeconds,
}) {
  const safeBase = Math.max(0, Number(baseSeconds) || 0);
  if (safeBase <= 0) return 0;

  const safeRound = Math.max(1, Number(round) || 1);
  const safeMax = Math.max(safeBase, Number(maxSeconds) || safeBase);
  const normalized = String(strategy || 'fixed').trim().toLowerCase();
  if (normalized === 'exponential') {
    const factor = 2 ** Math.max(0, safeRound - 1);
    return Math.min(safeMax * 1000, safeBase * factor * 1000);
  }
  return safeBase * 1000;
}

export async function waitForNextRound({
  round,
  maxRounds,
  baseSeconds,
  strategy = 'fixed',
  maxSeconds = baseSeconds,
  sleeper = sleep,
}) {
  if ((Number(round) || 0) >= (Number(maxRounds) || 0)) {
    return 0;
  }
  const waitMs = resolveRoundWaitMs({ round, baseSeconds, strategy, maxSeconds });
  if (waitMs > 0) {
    await sleeper(waitMs);
  }
  return waitMs;
}
