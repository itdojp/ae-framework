import type { AppError } from './errors.js';

export function toErrorDetail(error: unknown): string {
  if (error instanceof Error) {
    return error.message;
  }
  if (typeof error === 'string') {
    return error;
  }
  try {
    const serialized = JSON.stringify(error);
    return typeof serialized === 'string' ? serialized : String(error);
  } catch {
    return String(error);
  }
}

export function toExecAppError(step: string, error: unknown): AppError {
  return {
    code: 'E_EXEC',
    step,
    detail: toErrorDetail(error),
  };
}

export function formatAppError(error: AppError): string {
  switch (error.code) {
    case 'E_EXEC':
      return `[${error.code}] step=${error.step}${error.detail ? ` detail=${error.detail}` : ''}`;
    case 'E_PARSE':
      return `[${error.code}] step=${error.step}${error.detail ? ` detail=${error.detail}` : ''}`;
    case 'E_TIMEOUT':
      return `[${error.code}] step=${error.step} ms=${error.ms}`;
    case 'E_CONFIG':
      return `[${error.code}] key=${error.key}${error.detail ? ` detail=${error.detail}` : ''}`;
    default: {
      const exhaustive: never = error;
      return String(exhaustive);
    }
  }
}
