import { afterEach, describe, expect, it } from 'vitest';
import { buildProvenance } from '../../../scripts/ci/write-verify-lite-assurance-provenance.mjs';

const ENV_KEYS = [
  'GITHUB_REPOSITORY',
  'GITHUB_WORKFLOW',
  'GITHUB_RUN_ID',
  'GITHUB_RUN_ATTEMPT',
  'GITHUB_EVENT_NAME',
  'GITHUB_SHA',
  'VERIFY_LITE_PR_HEAD_SHA',
];

const originalEnv = new Map(ENV_KEYS.map((key) => [key, process.env[key]]));

afterEach(() => {
  for (const key of ENV_KEYS) {
    const original = originalEnv.get(key);
    if (original === undefined) {
      delete process.env[key];
    } else {
      process.env[key] = original;
    }
  }
});

describe('verify-lite assurance provenance writer', () => {
  it('records the pull request head SHA instead of the pull_request merge commit SHA', () => {
    process.env.GITHUB_REPOSITORY = 'itdojp/ae-framework';
    process.env.GITHUB_WORKFLOW = 'Verify Lite';
    process.env.GITHUB_RUN_ID = '123456789';
    process.env.GITHUB_RUN_ATTEMPT = '1';
    process.env.GITHUB_EVENT_NAME = 'pull_request';
    process.env.GITHUB_SHA = 'merge-commit-sha';
    process.env.VERIFY_LITE_PR_HEAD_SHA = 'pr-head-sha';

    const provenance = buildProvenance('artifacts/assurance/claim-evidence-provenance.json');

    expect(provenance.source.sha).toBe('pr-head-sha');
    expect(provenance.workflow.runId).toBe('123456789');
    expect(provenance.artifact.manifestPath).toBe('artifacts/assurance/claim-evidence-manifest.json');
  });
});
