import fs from 'node:fs';
import path from 'node:path';
import yaml from 'js-yaml';
import { describe, expect, it } from 'vitest';

type WorkflowDocument = {
  permissions?: Record<string, string>;
};

const workflowPath = path.resolve(process.cwd(), '.github/workflows/phase6-validation.yml');
const rawWorkflow = () => fs.readFileSync(workflowPath, 'utf8');
const parseWorkflow = () => yaml.load(rawWorkflow()) as WorkflowDocument;

describe('phase6 validation workflow security', () => {
  it('runs pull_request validation with read-only permissions', () => {
    expect(parseWorkflow().permissions).toEqual({ contents: 'read' });
  });

  it('does not expose the Lighthouse CI app token to checked-out PR code', () => {
    const workflow = rawWorkflow();

    expect(workflow).not.toContain('LHCI_GITHUB_APP_TOKEN');
    expect(workflow).not.toContain('secrets.LHCI_GITHUB_APP_TOKEN');
    expect(workflow).toContain('lhci autorun --config=./configs/lighthouserc.cjs');
  });

  it('disables persisted checkout credentials in all Phase 6 jobs', () => {
    const workflow = rawWorkflow();
    const checkoutCount = (workflow.match(/uses: actions\/checkout@v4/g) ?? []).length;
    const persistFalseCount = (workflow.match(/persist-credentials: false/g) ?? []).length;

    expect(checkoutCount).toBeGreaterThan(0);
    expect(persistFalseCount).toBe(checkoutCount);
  });
});
