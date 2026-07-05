import fs from 'node:fs';
import path from 'node:path';
import { describe, expect, it } from 'vitest';
import yaml from 'js-yaml';

const repoRoot = process.cwd();
const workflowPath = path.join(repoRoot, '.github/workflows/deploy-time-profiles-recorded-replay.yml');

describe('deploy-time profile recorded replay workflow', () => {
  it('runs recorded-PR replay only on schedule or manual dispatch', () => {
    const raw = fs.readFileSync(workflowPath, 'utf8');
    const workflow = yaml.load(raw) as any;
    const job = workflow.jobs?.['recorded-replay'];

    expect(workflow.name).toBe('Deploy-Time Profiles Recorded Replay');
    expect(workflow.on?.pull_request).toBeUndefined();
    expect(workflow.on?.push).toBeUndefined();
    expect(workflow.on?.workflow_dispatch).toBeDefined();
    expect(workflow.on?.schedule?.[0]?.cron).toBe('27 18 * * *');
    expect(job?.name).toBe('deploy-time-profiles-recorded-replay');
    expect(raw).toContain('pnpm -s run profiles:validate');
    expect(raw).toContain('pnpm -s run profiles:dogfood:recorded -- \\');
    expect(raw).toContain('--profile all');
    expect(raw).toContain('deploy-time-profiles-recorded-report.json');
    expect(raw).toContain('deploy-time-profiles-recorded-report.md');
    expect(raw).toContain('actions/upload-artifact@v4');
  });
});
