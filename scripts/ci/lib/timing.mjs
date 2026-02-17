export function sleep(ms) {
  const waitMs = Number.isFinite(ms) ? Math.max(0, Math.trunc(ms)) : 0;
  return new Promise((resolve) => setTimeout(resolve, waitMs));
}
