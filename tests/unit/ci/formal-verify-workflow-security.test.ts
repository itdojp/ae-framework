import fs from 'node:fs';
import path from 'node:path';
import { describe, expect, it } from 'vitest';
import yaml from 'js-yaml';

type WorkflowDocument = {
  on?: {
    workflow_dispatch?: {
      inputs?: Record<string, any>;
    };
  };
  permissions?: Record<string, string>;
  jobs?: Record<string, any>;
};

const workflowPath = path.resolve(process.cwd(), '.github/workflows/formal-verify.yml');
const rawWorkflow = () => fs.readFileSync(workflowPath, 'utf8');
const parseWorkflow = () => yaml.load(rawWorkflow()) as WorkflowDocument;

describe('formal-verify workflow dispatch security', () => {
  it('uses finite choices for dispatch target, engine, and solver', () => {
    const workflow = parseWorkflow();
    const inputs = workflow.on?.workflow_dispatch?.inputs ?? {};

    expect(inputs.target?.type).toBe('choice');
    expect(inputs.target?.options).toEqual([
      'all',
      'conformance',
      'alloy',
      'tla',
      'smt',
      'apalache',
      'kani',
      'spin',
      'csp',
      'lean',
    ]);
    expect(inputs.engine?.type).toBe('choice');
    expect(inputs.engine?.options).toEqual(['tlc', 'apalache']);
    expect(inputs.solver?.type).toBe('choice');
    expect(inputs.solver?.options).toEqual(['z3', 'cvc5']);
  });

  it('removes jar path dispatch inputs and direct shell interpolation of tlaFile', () => {
    const workflow = rawWorkflow();
    const inputs = parseWorkflow().on?.workflow_dispatch?.inputs ?? {};

    expect(inputs.alloyJar).toBeUndefined();
    expect(inputs.tlaToolsJar).toBeUndefined();
    expect(workflow).not.toContain('ALLOY_RUN_CMD');
    expect(workflow).not.toContain("TLA_TOOLS_JAR: ''");
    expect(workflow).not.toMatch(/run:\s*\|[\s\S]*\$\{\{\s*inputs\.tlaFile/);
    expect(workflow).toContain('TLA_FILE: ${{ github.event_name == \'workflow_dispatch\' && inputs.tlaFile || \'spec/tla/DomainSpec.tla\' }}');
    expect(workflow).toContain('APALACHE_FILE: ${{ github.event_name == \'workflow_dispatch\' && inputs.tlaFile || \'spec/tla/DomainSpec.tla\' }}');
  });

  it('restores a trusted TLC jar path without exposing a dispatch jar override', () => {
    const workflow = rawWorkflow();

    expect(workflow).toContain("TLA_TOOLS_VERSION: '1.8.0'");
    expect(workflow).toContain('key: ${{ runner.os }}-tla2tools-${{ env.TLA_TOOLS_VERSION }}');
    expect(workflow).toContain('https://github.com/tlaplus/tlaplus/releases/download/v${TLA_TOOLS_VERSION}/tla2tools.jar');
    expect(workflow).toContain("TLA_TOOLS_JAR: ${{ format('{0}/.cache/tools/tla2tools.jar', github.workspace) }}");
  });

  it('uses least-privilege permissions and disables persisted checkout credentials', () => {
    const workflow = rawWorkflow();
    const parsed = parseWorkflow();
    const checkoutCount = (workflow.match(/uses: actions\/checkout@v4/g) ?? []).length;
    const persistFalseCount = (workflow.match(/persist-credentials: false/g) ?? []).length;

    expect(parsed.permissions).toEqual({ contents: 'read' });
    expect(checkoutCount).toBeGreaterThan(0);
    expect(persistFalseCount).toBe(checkoutCount);
  });

  it('authorizes workflow_dispatch actors before each formal job can execute repository scripts', () => {
    const workflow = rawWorkflow();
    const checkoutCount = (workflow.match(/uses: actions\/checkout@v4/g) ?? []).length;
    const authCount = (workflow.match(/node scripts\/ci\/assert-workflow-dispatch-actor\.mjs/g) ?? []).length;

    expect(authCount).toBe(checkoutCount);
    expect(workflow).toContain("if: ${{ github.event_name == 'workflow_dispatch' }}");
  });
});
