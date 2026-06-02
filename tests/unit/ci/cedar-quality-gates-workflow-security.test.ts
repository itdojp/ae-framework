import fs from 'node:fs';
import path from 'node:path';
import yaml from 'js-yaml';
import { describe, expect, it } from 'vitest';

type WorkflowDocument = {
  jobs?: Record<string, any>;
};

const workflowPath = path.resolve(process.cwd(), '.github/workflows/cedar-quality-gates.yml');
const rawWorkflow = () => fs.readFileSync(workflowPath, 'utf8');
const parseWorkflow = () => yaml.load(rawWorkflow()) as WorkflowDocument;

describe('cedar quality gates workflow security', () => {
  it('keeps validation read-only and isolates PR comment write permissions', () => {
    const jobs = parseWorkflow().jobs ?? {};

    expect(jobs['cedar-validate']?.permissions).toEqual({ contents: 'read' });
    expect(jobs['cedar-comment']?.permissions).toEqual({
      contents: 'read',
      issues: 'write',
      'pull-requests': 'write',
    });
  });

  it('does not consume stale summaries or continue after validator process failures', () => {
    const workflow = rawWorkflow();

    expect(workflow).toContain('rm -f "$CEDAR_SUMMARY"');
    expect(workflow).toContain('node scripts/policies/validate-cedar.mjs');
    expect(workflow).toContain('node scripts/policies/cedar-summary-guard.mjs --summary "$CEDAR_SUMMARY" --write-output');
    expect(workflow).not.toContain('node scripts/policies/validate-cedar.mjs || true');
  });

  it('uses checked-in guard logic for Cedar enforcement instead of shell interpolation of outputs', () => {
    const jobs = parseWorkflow().jobs ?? {};
    const enforceStep = jobs['cedar-validate']?.steps?.find((step: any) => step.name === 'Enforce cedar (errors==0)');
    const workflow = rawWorkflow();

    expect(enforceStep?.run).toBe('node scripts/policies/cedar-summary-guard.mjs --summary "$CEDAR_SUMMARY" --enforce');
    expect(enforceStep?.run).not.toContain('${{');
    expect(workflow).not.toMatch(/::error::Cedar validation found NG=\$\{\{/);
  });

  it('reports invalid comment summaries instead of coercing rejected counts to zero', () => {
    const workflow = rawWorkflow();

    expect(workflow).toContain('Cedar summary artifact was invalid:');
    expect(workflow).toContain('must be a non-negative safe integer');
    expect(workflow).not.toContain('Number.isSafeInteger(value) && value >= 0 ? value : 0');
  });

  it('keeps the Cedar PR comment heading consistent with enforcement mode', () => {
    const workflow = rawWorkflow();

    expect(workflow).toContain("const enforced = labels.includes('enforce-security');");
    expect(workflow).toContain("`### Cedar Policies (${enforced ? 'enforced' : 'report-only'})\\n\\n`");
    expect(workflow).not.toContain("let body = header + '### Cedar Policies (report-only)");
  });
});
