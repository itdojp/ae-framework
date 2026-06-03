import { describe, expect, it, vi } from 'vitest';

const childProcessMock = vi.hoisted(() => ({
  execFileSync: vi.fn(() => ''),
}));

vi.mock('child_process', () => ({
  execFileSync: childProcessMock.execFileSync,
}));

vi.mock('node:child_process', () => ({
  execFileSync: childProcessMock.execFileSync,
}));

describe('validation task adapter construction', () => {
  it('constructs without probing verifier tools or starting processes', async () => {
    childProcessMock.execFileSync.mockClear();
    const { ValidationTaskAdapter } = await import('../../../src/agents/validation-task-adapter.js');

    new ValidationTaskAdapter();

    expect(childProcessMock.execFileSync).not.toHaveBeenCalled();
  });

  it('constructs the CodeX task handler without verifier process execution', async () => {
    childProcessMock.execFileSync.mockClear();
    const { createCodexTaskAdapter } = await import('../../../src/agents/codex-task-adapter.js');

    createCodexTaskAdapter();

    expect(childProcessMock.execFileSync).not.toHaveBeenCalled();
  });
});
