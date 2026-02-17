import { describe, expect, it } from 'vitest';
import {
  buildFailureMessage,
  detectPackageManager,
  evaluatePackageManager,
} from '../../../scripts/ci/check-package-manager.mjs';

describe('check-package-manager', () => {
  it('detects pnpm from npm_config_user_agent', () => {
    const manager = detectPackageManager({
      npm_config_user_agent: 'pnpm/10.0.0 npm/? node/v20.11.1',
    });
    expect(manager).toBe('pnpm');
  });

  it('allows pnpm when user agent is missing but npm_execpath points to pnpm', () => {
    const result = evaluatePackageManager({
      npm_execpath: '/usr/local/lib/node_modules/pnpm/bin/pnpm.cjs',
    });
    expect(result.ok).toBe(true);
    expect(result.reason).toBe('pnpm_detected');
  });

  it('rejects npm and shows migration instructions', () => {
    const result = evaluatePackageManager({
      npm_config_user_agent: 'npm/10.8.1 node/v20.11.1',
      npm_execpath: '/usr/local/lib/node_modules/npm/bin/npm-cli.js',
    });

    expect(result.ok).toBe(false);
    expect(result.detectedManager).toBe('npm');

    const message = buildFailureMessage(result);
    expect(message).toContain('requires pnpm');
    expect(message).toContain('corepack enable');
    expect(message).toContain('pnpm install');
    expect(message).toContain('workspace:*');
  });

  it('allows when runtime metadata is unavailable', () => {
    const result = evaluatePackageManager({});
    expect(result.ok).toBe(true);
    expect(result.reason).toBe('missing_runtime_metadata');
  });
});
