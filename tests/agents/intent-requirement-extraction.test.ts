import { describe, expect, it } from 'vitest';
import {
  extractRequirementsFromSources,
  parseStructuredRequirements,
} from '../../src/agents/intent-requirement-extraction';

describe('intent requirement extraction', () => {
  it('extracts requirement-like statements from mixed source types', () => {
    const extracted = extractRequirementsFromSources([
      {
        type: 'document',
        content: [
          '1. The system must encrypt all data at rest',
          '- Users should authenticate via SSO',
          'This is a non-requirement memo line',
        ].join('\n'),
      },
      {
        type: 'conversation',
        content: 'I need approval workflows. We want audit logging.',
      },
      {
        type: 'email',
        content: 'Users must be able to export monthly reports.',
      },
    ]);

    expect(extracted).toContain('The system must encrypt all data at rest');
    expect(extracted).toContain('Users should authenticate via SSO');
    expect(extracted).toContain('approval workflows. We want audit logging.');
    expect(extracted).toContain('audit logging.');
    expect(extracted).toContain('export monthly reports.');
  });

  it('builds structured requirements with deterministic id/type/category/priority', () => {
    const requirements = parseStructuredRequirements([
      'The system must provide API integration for partners',
      'Security policy compliance is required for all requests',
      'Response time should be under 200ms',
    ]);

    expect(requirements).toHaveLength(3);

    expect(requirements[0]).toMatchObject({
      id: 'REQ-001',
      type: 'technical',
      category: 'api',
      priority: 'must',
      source: 'extracted',
      status: 'draft',
    });

    expect(requirements[1]).toMatchObject({
      id: 'REQ-002',
      type: 'non-functional',
      category: 'security',
      priority: 'should',
    });

    expect(requirements[2]).toMatchObject({
      id: 'REQ-003',
      type: 'non-functional',
      category: 'general',
      priority: 'should',
    });
  });
});
