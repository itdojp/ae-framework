import { describe, expect, it, vi } from 'vitest';

import { UIUXAgentAdapter } from '../../../src/agents/adapters/ui-ux-agent-adapter';
import { UIUXTaskAdapter } from '../../../src/agents/ui-ux-task-adapter';
import type { UIUXInput } from '../../../src/agents/interfaces/standard-interfaces';

function createInput(overrides: Partial<UIUXInput> = {}): UIUXInput {
  return {
    domainModel: {
      entities: [
        {
          name: 'Order',
          attributes: [{ name: 'id', type: 'string', required: true }],
          methods: [],
          invariants: [],
          isAggregateRoot: true,
        },
      ],
      relationships: [],
      valueObjects: [],
      aggregates: [],
      services: [],
      boundedContexts: [],
    },
    userStories: {
      stories: [
        {
          id: 'US-1',
          title: 'Create order',
          description: 'As a user I want to create an order so that I can submit it',
          asA: 'user',
          iWant: 'create an order',
          soThat: 'I can submit it',
          acceptanceCriteria: ['Order is created successfully'],
          priority: 'high',
        },
      ],
      acceptanceCriteria: [],
      traceabilityMatrix: { requirements: { 'req-1': ['US-1'] }, coverage: 100, gaps: [] },
      success: true,
    },
    stakeholders: [
      {
        name: 'End User',
        role: 'consumer',
        concerns: ['usability'],
        influenceLevel: 'high',
      },
    ],
    ...overrides,
  };
}

describe('UIUXTaskAdapter', () => {
  it('classifyTask recognizes wireframe intent', () => {
    const adapter = new UIUXTaskAdapter();
    const taskType = (adapter as any).classifyTask(
      'チェックアウト画面の wireframe を作成する',
      'Need wireframe for checkout flow.',
    );
    expect(taskType).toBe('wireframe');
  });

  it('classifyTask recognizes Japanese user-flow keywords', () => {
    const adapter = new UIUXTaskAdapter();
    const taskType = (adapter as any).classifyTask(
      '画面遷移を設計する',
      'ユーザーフローを整理してほしい',
    );
    expect(taskType).toBe('user-flow');
  });

  it('generateUIUXArtifacts returns structured output and score', async () => {
    const adapter = new UIUXTaskAdapter();
    const result = await adapter.generateUIUXArtifacts(createInput());

    expect(result.output.wireframes.length).toBeGreaterThan(0);
    expect(result.output.components.length).toBeGreaterThan(0);
    expect(result.qualityScore).toBeGreaterThanOrEqual(50);
  });

  it('generateUIUXArtifacts emits warnings for sparse input', async () => {
    const adapter = new UIUXTaskAdapter();
    const result = await adapter.generateUIUXArtifacts(
      createInput({
        stakeholders: [],
        userStories: {
          stories: [],
          acceptanceCriteria: [],
          traceabilityMatrix: { requirements: {}, coverage: 0, gaps: ['no stories'] },
          success: true,
        },
      }),
    );

    expect(result.warnings.some((message) => message.includes('No stakeholders'))).toBe(true);
    expect(result.warnings.some((message) => message.includes('No user stories'))).toBe(true);
  });

  it('generateUserFlows omits nextStep for terminal step', async () => {
    const adapter = new UIUXTaskAdapter();
    const result = await adapter.generateUIUXArtifacts(
      createInput({
        userStories: {
          stories: [
            {
              id: 'US-1',
              title: 'Create order',
              description: 'As a user I want to create an order',
              asA: 'user',
              iWant: 'create order',
              soThat: 'I can submit it',
              acceptanceCriteria: ['Order can be created'],
              priority: 'high',
            },
            {
              id: 'US-2',
              title: 'List orders',
              description: 'As a user I want to list orders',
              asA: 'user',
              iWant: 'list orders',
              soThat: 'I can review them',
              acceptanceCriteria: ['Orders can be listed'],
              priority: 'medium',
            },
          ],
          acceptanceCriteria: [],
          traceabilityMatrix: { requirements: { 'req-1': ['US-1'], 'req-2': ['US-2'] }, coverage: 100, gaps: [] },
          success: true,
        },
      }),
    );

    const mainFlow = result.output.userFlows.find((flow) => flow.name === 'Main User Flow');
    const lastStep = mainFlow?.steps[mainFlow.steps.length - 1];
    expect(lastStep).toBeDefined();
    expect(lastStep?.nextStep).toBeUndefined();
  });

  it('generateUIUXArtifacts continues when API spec inference fails', async () => {
    const adapter = new UIUXTaskAdapter();
    vi.spyOn((adapter as any).agent, 'createAPISpecification').mockRejectedValue(new Error('api-spec failed'));

    const result = await adapter.generateUIUXArtifacts(createInput());
    expect(result.output.wireframes.length).toBeGreaterThan(0);
    expect(result.warnings.some((message) => message.includes('API-style endpoint inference failed'))).toBe(true);
  });
});

describe('UIUXAgentAdapter', () => {
  it('process returns generated artifacts without placeholder warning', async () => {
    const adapter = new UIUXAgentAdapter();
    const result = await adapter.process(createInput());

    expect(result.success).toBe(true);
    expect(result.data.wireframes.length).toBeGreaterThan(0);
    expect((result.warnings || []).join(' ').toLowerCase()).not.toContain('placeholder');
  });

  it('process returns standardized error when task adapter throws', async () => {
    const adapter = new UIUXAgentAdapter();
    vi.spyOn((adapter as any).uiuxTaskAdapter, 'generateUIUXArtifacts').mockRejectedValue(new Error('test failure'));

    const result = await adapter.process(createInput());

    expect(result.success).toBe(false);
    expect(result.errors?.[0]?.message).toContain('test failure');
    expect(result.errors?.[0]?.code).toBe('UI_UX_GENERATION_ERROR');
  });
});
