import { describe, it, expect } from 'vitest';
import { commandExists, runCommand, resolveCommandPath } from '../../scripts/formal/verify-apalache.mjs';

describe('verify-apalache command utils', () => {
  it('detects existing and missing commands', () => {
    expect(commandExists('node')).toBe(true);
    expect(commandExists('definitely-not-a-real-command-12345')).toBe(false);
  });

  it('captures output and status for executed commands', () => {
    const ok = runCommand('node', ['-e', 'process.stdout.write("ok")']);
    expect(ok.available).toBe(true);
    expect(ok.output).toContain('ok');

    const fail = runCommand('node', ['-e', 'process.exit(2)']);
    expect(fail.available).toBe(true);
    expect(fail.status).toBe(2);
  });

  it('resolves command path when which is available', () => {
    if (!commandExists('which')) return;
    const resolved = resolveCommandPath('node');
    expect(resolved.length).toBeGreaterThan(0);
  });
});
