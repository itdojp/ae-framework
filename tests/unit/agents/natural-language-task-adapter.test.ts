import { describe, expect, it } from 'vitest';

import { NaturalLanguageTaskAdapter } from '../../../src/agents/natural-language-task-adapter.js';

describe('NaturalLanguageTaskAdapter conflict detection', () => {
  it('detects modality conflicts on similar requirements', async () => {
    const adapter = new NaturalLanguageTaskAdapter();
    const result = await adapter.processNaturalLanguageRequirements(
      [
        'The system must archive audit logs for one year.',
        'The system may archive audit logs for one year.',
      ].join(' '),
    );

    expect(result.conflicts.some((conflict) => conflict.includes('modality differs'))).toBe(true);
  });

  it('detects access intent conflicts on similar requirements', async () => {
    const adapter = new NaturalLanguageTaskAdapter();
    const result = await adapter.processNaturalLanguageRequirements(
      [
        'The admin role must allow exporting all audit logs.',
        'The admin role must prohibit exporting all audit logs.',
      ].join(' '),
    );

    expect(result.conflicts.some((conflict) => conflict.includes('Permission intent differs'))).toBe(true);
  });

  it('detects access conflicts when requirements use disallow wording', async () => {
    const adapter = new NaturalLanguageTaskAdapter();
    const result = await adapter.processNaturalLanguageRequirements(
      [
        'The admin role must disallow exporting all audit logs.',
        'The admin role must allow exporting all audit logs.',
      ].join(' '),
    );

    expect(result.conflicts.some((conflict) => conflict.includes('Permission intent differs'))).toBe(true);
  });

  it('detects incompatible numeric constraints', async () => {
    const adapter = new NaturalLanguageTaskAdapter();
    const result = await adapter.processNaturalLanguageRequirements(
      [
        'API response time must be less than 2 seconds.',
        'API response time must be at least 5 seconds.',
      ].join(' '),
    );

    expect(result.conflicts.some((conflict) => conflict.includes('Numeric constraints are incompatible'))).toBe(
      true,
    );
  });

  it('detects incompatible numeric constraints across minute and second units', async () => {
    const adapter = new NaturalLanguageTaskAdapter();
    const result = await adapter.processNaturalLanguageRequirements(
      [
        'API response time must be at most 2 minutes for checkout requests.',
        'API response time must be at least 180 seconds for checkout requests.',
      ].join(' '),
    );

    expect(result.conflicts.some((conflict) => conflict.includes('Numeric constraints are incompatible'))).toBe(
      true,
    );
  });

  it('detects conflicts for japanese requirements using deny and allow intent', async () => {
    const adapter = new NaturalLanguageTaskAdapter();
    const result = await adapter.processNaturalLanguageRequirements(
      [
        '管理者は監査ログの削除を禁止する必要がある.',
        '管理者は監査ログの削除を許可する必要がある.',
      ].join(' '),
    );

    expect(result.conflicts.some((conflict) => conflict.includes('Permission intent differs'))).toBe(true);
  });

  it('does not flag unrelated requirements as conflicts', async () => {
    const adapter = new NaturalLanguageTaskAdapter();
    const result = await adapter.processNaturalLanguageRequirements(
      [
        'The system must support dark mode preferences.',
        'Revenue reports should include monthly totals.',
      ].join(' '),
    );

    expect(result.conflicts).toEqual([]);
  });
});
