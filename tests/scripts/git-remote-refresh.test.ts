import { describe, expect, it } from 'vitest';
import { pathToFileURL } from 'node:url';
import { resolve } from 'node:path';

const repoRoot = resolve('.');
const moduleUrl = pathToFileURL(resolve(repoRoot, 'scripts/maintenance/git-remote-refresh.mjs')).href;

describe.sequential('git-remote-refresh helpers', () => {
  it('derives unique fetch remotes from analysis remote and base ref', async () => {
    const mod = await import(moduleUrl);

    expect(mod.deriveFetchRemotes('origin', 'origin/main')).toEqual(['origin']);
    expect(mod.deriveFetchRemotes('origin', 'upstream/main')).toEqual(['origin', 'upstream']);
    expect(mod.deriveFetchRemotes('origin', 'refs/remotes/upstream/main')).toEqual([
      'origin',
      'upstream',
    ]);
  });

  it('returns structured failure details instead of throwing on fetch failure', async () => {
    const mod = await import(moduleUrl);

    const result = mod.refreshRemoteTrackingRefs('origin', {
      gitRunner: () => ({
        ok: false,
        output: 'fatal: network error',
        message: 'fetch failed',
      }),
    });

    expect(result).toEqual({
      attempted: true,
      ok: false,
      remote: 'origin',
      output: 'fatal: network error',
      message: 'failed to fetch remote origin: fatal: network error',
    });
  });
});
