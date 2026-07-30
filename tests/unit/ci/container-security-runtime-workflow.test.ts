import fs from 'node:fs';
import path from 'node:path';
import { describe, expect, it } from 'vitest';
import yaml from 'js-yaml';

const workflowPath = path.resolve(process.cwd(), '.github/workflows/security.yml');
const workflowText = fs.readFileSync(workflowPath, 'utf8');
const workflow = yaml.load(workflowText) as any;
const job = workflow.jobs['container-security'];
const steps = job.steps as any[];
const step = (name: string) => steps.find((candidate) => candidate.name === name);
const stepIndex = (name: string) => steps.findIndex((candidate) => candidate.name === name);

describe('Container Security runtime workflow', () => {
  it('keeps normal trusted events enforced and fails closed when the manifest disappears', () => {
    expect(workflow.on.push).toBeDefined();
    expect(workflow.on.schedule).toBeDefined();
    expect(workflow.on.workflow_dispatch).toBeDefined();
    expect(job.if).toContain("needs.gate.outputs.run_container_security == 'true'");
    expect(job.if).toContain("github.event_name != 'pull_request'");
    expect(stepIndex('Verify runner container runtime')).toBeLessThan(stepIndex('Require container manifest'));
    expect(stepIndex('Require container manifest')).toBeLessThan(stepIndex('Build container image'));
    expect(step('Require container manifest').run).toContain('--stage manifest-detect');
    expect(step('Require container manifest').run).toContain('outcome=failure');
    expect(step('Verify runner container runtime').run).toContain('steps.container_manifest.outputs.dockerfile');
    expect(job['continue-on-error']).toBeUndefined();
  });

  it('separates focused dispatch evidence without weakening normal push or schedule execution', () => {
    const input = workflow.on.workflow_dispatch.inputs.mode;
    const gateScript = workflow.jobs.gate.steps.find((candidate: any) => candidate.id === 'lbl').with.script;
    expect(input.required).toBe(true);
    expect(input.default).toBe('all');
    expect(input.options).toEqual(['all', 'container-security']);
    expect(workflow.on.workflow_dispatch.inputs.expected_head.required).toBe(false);
    expect(gateScript).toContain("context.eventName === 'workflow_dispatch'");
    expect(gateScript).toContain("context.payload.inputs?.mode === 'container-security'");
    expect(gateScript).toContain("/^[a-f0-9]{40}$/");
    expect(gateScript).toContain('expectedHead !== context.sha');
    expect(gateScript).toContain('core.setFailed');
    expect(gateScript).toContain('const runSecurity = normalSecurityAllowed && !focusedContainer');
    expect(gateScript).toContain('const runContainerSecurity = normalSecurityAllowed');
    expect(workflow.jobs.gate.outputs.run_container_security).toContain('steps.lbl.outputs.run_container_security');
    expect(workflow.on.push).toBeDefined();
    expect(workflow.on.schedule).toBeDefined();
  });

  it('uses a bounded runner preflight before repository build without mutating the hosted tuple', () => {
    expect(stepIndex('Verify runner container runtime')).toBeLessThan(stepIndex('Build container image'));
    expect(step('Verify runner container runtime').run).toContain('container-runtime-preflight.mjs preflight');
    expect(step('Verify runner container runtime').run).toContain('--runtime "${CONTAINER_RUNTIME}"');
    expect(workflowText).not.toContain('sudo apt-get install -y podman');
    expect(job['timeout-minutes']).toBe(45);
  });

  it('includes Container Security failures in scheduled notification dependencies', () => {
    expect(workflow.jobs['security-notification'].needs).toContain('container-security');
    expect(workflow.jobs['security-notification'].if).toContain("github.event_name == 'schedule'");
  });

  it('binds repository build and Trivy execution to the verified runtime path', () => {
    expect(step('Build container image').run).toContain('steps.runtime_preflight.outputs.podman_path');
    expect(step('Build container image').run).toContain('steps.runtime_preflight.outputs.runtime_path');
    expect(step('Run Trivy vulnerability scanner').run).toContain('steps.runtime_preflight.outputs.runtime_path');
    expect(step('Verify production image user').run).toContain('--expect-stdout nextjs');
  });

  it('pins newly controlled smoke and scanner images by digest', () => {
    expect(job.env.MINIMAL_RUNTIME_IMAGE).toMatch(/^docker\.io\/.*@sha256:[a-f0-9]{64}$/);
    expect(job.env.TRIVY_IMAGE).toMatch(/^ghcr\.io\/.*@sha256:[a-f0-9]{64}$/);
    expect(job.env.TRIVY_IMAGE).toContain(':0.72.0@');
  });

  it('fails closed on archive/SARIF gaps and records the upload outcome', () => {
    expect(step('Export image archive').run).toContain('--kind archive');
    expect(step('Run Trivy vulnerability scanner').run).toContain('--kind sarif');
    expect(stepIndex('Run Trivy vulnerability scanner')).toBeLessThan(stepIndex('Upload Trivy scan results'));
    expect(step('Upload Trivy scan results').with.sarif_file).toBe('artifacts/container-security/trivy-results.sarif');
    expect(step('Upload Trivy scan results').if).toContain('success()');
    expect(step('Upload Trivy scan results').if).not.toContain('always()');
    expect(step('Record SARIF upload outcome').if).toContain('always()');
    expect(step('Record SARIF upload outcome').run).toContain('steps.sarif_upload.outcome');
    expect(workflowText).not.toContain('Note missing Trivy SARIF');
    expect(workflowText).not.toContain('skipping SARIF upload');
  });

  it('preserves checkout, permissions, scan, and failure semantics', () => {
    const checkout = steps.find((candidate) => candidate.uses === 'actions/checkout@v4');
    expect(checkout.with['persist-credentials']).toBe(false);
    expect(job.permissions).toEqual({
      contents: 'read',
      'security-events': 'write',
      actions: 'read',
    });
    expect(step('Upload Trivy scan results').uses).toBe('github/codeql-action/upload-sarif@v3');
    expect(workflowText).not.toContain('|| true');
    expect(workflowText).not.toContain('continue-on-error: ${{ github.event_name !=');
    expect(step('Upload container runtime diagnostic').with['if-no-files-found']).toBe('error');
  });

  it('retains the production image non-root boundary', () => {
    const dockerfile = fs.readFileSync(path.resolve(process.cwd(), 'podman/Dockerfile'), 'utf8');
    expect(dockerfile).toContain('USER nextjs');
    expect(dockerfile).toContain('adduser -S nextjs -u 1001');
  });
});
