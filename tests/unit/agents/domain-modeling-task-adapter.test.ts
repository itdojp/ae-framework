import { describe, expect, it, vi } from 'vitest';

import { DomainModelingTaskAdapter } from '../../../src/agents/domain-modeling-task-adapter';
import type { TaskRequest } from '../../../src/agents/task-types';

function createRequest(description: string, prompt: string): TaskRequest {
  return {
    description,
    prompt,
    subagent_type: 'domain-modeling',
  };
}

describe('DomainModelingTaskAdapter input extraction', () => {
  it('classifyTask handles mixed Japanese/English prompts', () => {
    const adapter = new DomainModelingTaskAdapter();
    const taskType = (adapter as any).classifyTask(
      'エンティティ識別を進めたい',
      'Please identify entities and relationships for the sales domain.',
    );

    expect(taskType).toBe('identify-entities');
  });

  it('extractEntityInput populates structured fields from prompt sections', () => {
    const adapter = new DomainModelingTaskAdapter();
    const input = (adapter as any).extractEntityInput(`
Entities: Customer, Order, Payment
Business Rules: customer must be active, order total must be positive
Domain Services: ReservationService, BillingService
Relationships: Customer->Order, Order->Payment
`);

    expect(input.taskType).toBe('identify-entities');
    expect(input.entities).toEqual(expect.arrayContaining(['Customer', 'Order', 'Payment']));
    expect(input.businessRules).toEqual(
      expect.arrayContaining(['customer must be active', 'order total must be positive']),
    );
    expect(input.domainServices).toEqual(expect.arrayContaining(['ReservationService', 'BillingService']));
    expect(input.relationships).toEqual(expect.arrayContaining(['Customer->Order', 'Order->Payment']));
  });

  it('extractEntityInput does not treat narrative sentence as entity section', () => {
    const adapter = new DomainModelingTaskAdapter();
    const input = (adapter as any).extractEntityInput(`
Identify entities for reservation domain.
Business Rules: reservation must have a valid guest
`);

    expect(input.entities).toEqual([]);
    expect(input.businessRules).toEqual(expect.arrayContaining(['reservation must have a valid guest']));
  });

  it('handleDomainModelingTask passes extracted input to identifyEntities', async () => {
    const adapter = new DomainModelingTaskAdapter();
    let capturedInput: any;
    (adapter as any).identifyEntities = vi.fn(async (input: unknown) => {
      capturedInput = input;
      return {
        entities: [{ name: 'Customer', type: 'entity', description: 'customer entity' }],
        aggregateRoots: ['Order'],
        valueObjects: ['Money'],
        domainServices: ['ReservationService'],
        relationships: [{ from: 'Customer', type: 'association', to: 'Order', cardinality: '1:n' }],
        businessRuleCoverage: [{ entity: 'Customer', rulesCount: 1 }],
        warnings: [],
      };
    });

    const response = await adapter.handleDomainModelingTask(
      createRequest(
        'エンティティ識別',
        'Identify entities. Entities: Customer, Order\nBusiness Rules: customer must be active',
      ),
    );

    expect((adapter as any).identifyEntities).toHaveBeenCalledTimes(1);
    expect(capturedInput.taskType).toBe('identify-entities');
    expect(capturedInput.entities).toEqual(expect.arrayContaining(['Customer', 'Order']));
    expect(response.summary).toContain('Entity Identification Complete');
  });
});
