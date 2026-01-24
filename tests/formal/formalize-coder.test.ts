import { describe, it, expect } from 'vitest';
import {
  FORMAL_CODER_REQUIRED_SECTIONS,
  buildCoderPrompt,
  renderTlaModule,
  type FormalPlan,
} from '../../packages/formalize-coder/src/index.js';

const samplePlan: FormalPlan = {
  schemaVersion: '0.1.0',
  metadata: {
    source: 'formalize-planner',
    generatedAt: '2026-01-01T00:00:00Z',
  },
  variables: [
    { name: 'tokens', type: 'Int' },
    { name: 'capacity', type: 'Int' },
  ],
  constants: [{ name: 'MAX', type: 'Int' }],
  actions: [
    { name: 'Init', tla: 'tokens = 0 /\\ capacity = MAX' },
    { name: 'Refill', tla: "tokens' = Min(MAX, tokens + 1)" },
  ],
  invariants: [{ name: 'CapInvariant', tla: 'tokens <= capacity' }],
  liveness: [{ name: 'EventuallyFull', tla: '<> (tokens = capacity)' }],
  assumptions: [{ name: 'NonNegative', tla: 'tokens >= 0' }],
};

describe('formalize-coder prompt', () => {
  it('includes module name and required sections', () => {
    const prompt = buildCoderPrompt({ plan: samplePlan, moduleName: 'TokenBucket' });
    expect(prompt).toContain('Module Name: TokenBucket');
    expect(prompt).toContain('schemaVersion');
    for (const section of FORMAL_CODER_REQUIRED_SECTIONS) {
      expect(prompt).toContain(section);
    }
  });
});

describe('formalize-coder renderer', () => {
  it('renders a TLA+ skeleton from the formal plan', () => {
    const moduleText = renderTlaModule(samplePlan, { moduleName: 'TokenBucket' });
    expect(moduleText).toContain('MODULE TokenBucket');
    expect(moduleText).toContain('EXTENDS');
    expect(moduleText).toContain('CONSTANTS');
    expect(moduleText).toContain('MAX');
    expect(moduleText).toContain('VARIABLES');
    expect(moduleText).toContain('tokens, capacity');
    expect(moduleText).toContain('Init == tokens = 0 /\\ capacity = MAX');
    expect(moduleText).toContain('Refill ==');
    expect(moduleText).toContain('Next ==');
    expect(moduleText).toContain('\\/ Refill');
    expect(moduleText).toContain('Spec == Init /\\ [][Next]_vars');
    expect(moduleText).toContain('CapInvariant == tokens <= capacity');
    expect(moduleText).toContain('EventuallyFull == <> (tokens = capacity)');
    expect(moduleText).toContain('NonNegative == tokens >= 0');
  });
});
