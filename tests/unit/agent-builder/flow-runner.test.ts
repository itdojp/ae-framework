import { describe, expect, it } from 'vitest';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { readFileSync } from 'node:fs';
import { executeFlow, loadFlowDefinition } from '../../../scripts/agent-builder/flow-runner.mjs';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

const flowFixture = path.resolve(__dirname, '../../../fixtures/flow/sample.flow.json');
const summaryFixture = path.resolve(
  __dirname,
  '../../../packages/envelope/__fixtures__/verify-lite-summary.json',
);

describe('agent builder flow runner', () => {
  it('loads and validates a flow definition', () => {
    const { flow } = loadFlowDefinition(flowFixture);
    expect(flow).toBeTruthy();
    expect(Array.isArray(flow.nodes)).toBe(true);
    expect(flow.nodes.length).toBeGreaterThan(0);
  });

  it('executes the flow and produces an envelope when summary is provided', () => {
    const { flow } = loadFlowDefinition(flowFixture);
    const summary = JSON.parse(readFileSync(summaryFixture, 'utf8'));

    const result = executeFlow(flow, {
      verifyLiteSummary: summary,
      generatedAt: '2025-01-01T00:00:00.000Z',
      correlation: {
        runId: 'run-123',
        workflow: 'agent-builder-adapter',
        commit: 'abc1234',
        branch: 'refs/heads/test',
        traceIds: ['trace-external'],
      },
    });

    expect(result.steps.length).toBe(flow.nodes.length);
    expect(result.outputs.spec).toBeDefined();
    expect(result.outputs.code).toBeDefined();
    expect(result.outputs.results).toBeDefined();
    expect(result.outputs.results.envelope).toBeDefined();
    expect(result.envelope?.traceCorrelation?.runId).toBe('run-123');
  });
});
