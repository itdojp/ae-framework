import { describe, expect, it, vi } from 'vitest';

import { FormalAgent } from '../../../src/agents/formal-agent.js';

describe('FormalAgent scaffold boundary', () => {
  it('generates a deterministic draft scaffold without invoking randomness', async () => {
    const random = vi.spyOn(Math, 'random').mockImplementation(() => {
      throw new Error('FormalAgent scaffold generation must not use randomness');
    });

    try {
      const agent = new FormalAgent({ generateDiagrams: false });
      const requirements = 'Inventory reservation must never make onHand negative.';
      const first = await agent.generateFormalSpecification(requirements, 'tla+');
      const second = await agent.generateFormalSpecification(requirements, 'tla+');

      expect(first.id).toBe(second.id);
      expect(first.id).toMatch(/^spec_[a-f0-9]{20}$/);
      expect(first.artifactStatus).toBe('draft');
      expect(first.content).toBe(second.content);
      expect(first.validation).toEqual(second.validation);
      expect(random).not.toHaveBeenCalled();
    } finally {
      random.mockRestore();
    }
  });

  it('does not expose a pseudo model-check method', () => {
    const agent = new FormalAgent();
    expect('runModelChecking' in agent).toBe(false);
  });
});
