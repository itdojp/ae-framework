import { describe, expect, it } from 'vitest';
import { formatAppError, toErrorDetail, toExecAppError } from '../../../src/core/command-errors';

describe('command-errors helpers', () => {
  it('normalizes unknown errors into detail strings', () => {
    expect(toErrorDetail(new Error('boom'))).toBe('boom');
    expect(toErrorDetail('plain')).toBe('plain');
    expect(toErrorDetail({ reason: 'x' })).toContain('reason');
    expect(toErrorDetail(undefined)).toBe('undefined');
    expect(toErrorDetail(Symbol('x'))).toBe('Symbol(x)');
  });

  it('handles serialization edge cases in toErrorDetail', () => {
    const circular: { self?: unknown } = {};
    circular.self = circular;

    expect(toErrorDetail(circular)).toBe(String(circular));
    expect(toErrorDetail(null)).toBe('null');
  });

  it('builds and formats E_EXEC errors', () => {
    const appError = toExecAppError('agent.complete', new Error('provider timeout'));
    expect(appError).toEqual({
      code: 'E_EXEC',
      step: 'agent.complete',
      detail: 'provider timeout',
    });
    expect(formatAppError(appError)).toContain('[E_EXEC]');
    expect(formatAppError(appError)).toContain('step=agent.complete');
  });

  it('formats non-exec AppError variants', () => {
    expect(formatAppError({ code: 'E_CONFIG', key: 'x', detail: 'invalid' })).toContain('[E_CONFIG]');
    expect(formatAppError({ code: 'E_TIMEOUT', step: 'verify', ms: 120000 })).toContain('ms=120000');
    expect(formatAppError({ code: 'E_PARSE', step: 'qa', detail: 'bad json' })).toContain('[E_PARSE]');

    const parseWithoutDetail = formatAppError({ code: 'E_PARSE', step: 'qa' });
    expect(parseWithoutDetail).toContain('[E_PARSE]');
    expect(parseWithoutDetail).not.toContain('undefined');
    expect(parseWithoutDetail).not.toContain('detail=');
  });
});
