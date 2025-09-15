export function isTestEnv(): boolean {
  return Boolean(
    process.env['VITEST'] ||
    process.env['NODE_ENV'] === 'test' ||
    process.env['AE_TEST_NO_EXIT'] === '1'
  );
}

export function safeExit(code: number = 0): void {
  if (isTestEnv()) return;
  // eslint-disable-next-line no-process-exit
  process.exit(code);
}

