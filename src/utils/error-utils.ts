export function toMessage(error: unknown): string {
  if (error instanceof Error) return error.message;
  if (typeof error === 'string') return error;
  try {
    return JSON.stringify(error);
  } catch {
    return String(error);
  }
}

export function toStack(error: unknown): string | undefined {
  return error instanceof Error ? error.stack : undefined;
}

