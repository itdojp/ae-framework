import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import type { LLM } from '../../src/providers/index.js';

const completeMock = vi.fn();
const safeExitMock = vi.fn();

vi.mock('../../src/providers/index.js', () => ({
  loadLLM: vi.fn(async (): Promise<LLM> => ({
    name: 'mock-llm',
    complete: completeMock,
  })),
}));

vi.mock('../../src/utils/safe-exit.js', () => ({
  safeExit: (...args: unknown[]) => safeExitMock(...args),
}));

const { agentComplete } = await import('../../src/commands/agent/complete.js');

describe('agentComplete redaction boundary', () => {
  let logSpy: ReturnType<typeof vi.spyOn>;
  let errorSpy: ReturnType<typeof vi.spyOn>;

  beforeEach(() => {
    completeMock.mockReset();
    safeExitMock.mockReset();
    logSpy = vi.spyOn(console, 'log').mockImplementation(() => {});
    errorSpy = vi.spyOn(console, 'error').mockImplementation(() => {});
  });

  afterEach(() => {
    logSpy.mockRestore();
    errorSpy.mockRestore();
  });

  it('TGT-009-F001: redacts prompt and response-like secrets before writing agent logs', async () => {
    completeMock.mockResolvedValueOnce(
      'provider answer Bearer raw-output-token password=raw-output-password',
    );

    await agentComplete('prompt token=raw-prompt-token and api_key=raw-prompt-key');

    const serializedLogs = JSON.stringify(logSpy.mock.calls);

    expect(serializedLogs).toContain('[REDACTED]');
    expect(serializedLogs).not.toContain('raw-prompt-token');
    expect(serializedLogs).not.toContain('raw-prompt-key');
    expect(serializedLogs).not.toContain('raw-output-token');
    expect(serializedLogs).not.toContain('raw-output-password');
    expect(errorSpy).not.toHaveBeenCalled();
    expect(safeExitMock).not.toHaveBeenCalled();
  });
});
