import { execFileSync } from 'node:child_process';

const DEFAULT_MAX_ATTEMPTS = 8;
const DEFAULT_INITIAL_DELAY_MS = 750;
const DEFAULT_MAX_DELAY_MS = 60_000;
// Add a small default spacing between gh calls to reduce secondary rate-limit bursts.
const DEFAULT_THROTTLE_MS = 250;

let lastGhInvocationAtMs = 0;

const toInteger = (value) => {
  if (value === null || value === undefined) return null;
  const raw = String(value).trim();
  if (!raw) return null;
  const parsed = Number(raw);
  if (!Number.isFinite(parsed)) return null;
  return Math.trunc(parsed);
};

const readEnvInt = (name, fallback) => {
  const parsed = toInteger(process.env[name]);
  if (parsed === null) return fallback;
  return parsed;
};

const sleepSync = (ms) => {
  if (!Number.isFinite(ms) || ms <= 0) return;
  if (process.env.AE_GH_RETRY_NO_SLEEP === '1') return;
  // Node >=20.11 (engines) supports Atomics.wait in the main thread.
  Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, ms);
};

const throttleSync = () => {
  const throttleMs = Math.max(0, readEnvInt('AE_GH_THROTTLE_MS', DEFAULT_THROTTLE_MS));
  if (throttleMs <= 0) return;
  const now = Date.now();
  const earliest = lastGhInvocationAtMs + throttleMs;
  if (earliest > now) {
    sleepSync(earliest - now);
  }
  lastGhInvocationAtMs = Date.now();
};

const shouldRetry = (text) => {
  const value = String(text || '');
  if (!value) return false;
  return (
    /\bHTTP\s+429\b/i.test(value) ||
    /exceeded retry limit/i.test(value) ||
    /too many requests/i.test(value) ||
    /secondary rate limit/i.test(value) ||
    /exceeded a secondary rate limit/i.test(value) ||
    /abuse detection/i.test(value)
  );
};

const buildFailureText = (error) => {
  const message = error && error.message ? String(error.message) : '';
  const stdout = error && error.stdout ? String(error.stdout) : '';
  const stderr = error && error.stderr ? String(error.stderr) : '';
  return [message, stderr, stdout].filter(Boolean).join('\n');
};

export function execGh(args, { input, encoding = 'utf8', cwd, env, stdio } = {}) {
  const maxAttempts = Math.max(1, readEnvInt('AE_GH_RETRY_MAX_ATTEMPTS', DEFAULT_MAX_ATTEMPTS));
  const initialDelay = Math.max(0, readEnvInt('AE_GH_RETRY_INITIAL_DELAY_MS', DEFAULT_INITIAL_DELAY_MS));
  const maxDelay = Math.max(initialDelay, readEnvInt('AE_GH_RETRY_MAX_DELAY_MS', DEFAULT_MAX_DELAY_MS));
  const resolvedStdio = stdio === undefined ? ['pipe', 'pipe', 'pipe'] : stdio;
  const debug = process.env.AE_GH_RETRY_DEBUG === '1';

  let delay = initialDelay;
  let lastError = null;

  for (let attempt = 1; attempt <= maxAttempts; attempt += 1) {
    try {
      throttleSync();
      return execFileSync('gh', args, {
        encoding,
        stdio: resolvedStdio,
        input,
        cwd,
        env,
      });
    } catch (error) {
      lastError = error;
      const failureText = buildFailureText(error);
      const retryable = shouldRetry(failureText);
      if (!retryable || attempt >= maxAttempts) {
        throw error;
      }
      if (debug) {
        process.stderr.write(
          `[gh-exec] retryable failure (attempt ${attempt}/${maxAttempts}); sleeping ${delay}ms\n`
        );
      }
      sleepSync(delay);
      delay = Math.min(maxDelay, Math.max(1, delay) * 2);
    }
  }

  // Defensive: the loop always throws or returns.
  throw lastError || new Error('gh failed');
}

export function execGhJson(args, { input, encoding = 'utf8', cwd, env } = {}) {
  const output = execGh(args, { input, encoding, cwd, env, stdio: ['pipe', 'pipe', 'pipe'] });
  return JSON.parse(output);
}

export function __testOnly_shouldRetry(text) {
  return shouldRetry(text);
}
