export const normalizeError = (error: unknown, fallbackMessage: string): Error => {
  if (error instanceof Error) return error;
  if (typeof error === 'string') return new Error(error);

  if (error && typeof error === 'object') {
    const record = error as Record<string, unknown>;
    const rawMessage = typeof record.message === 'string' ? record.message : null;
    let message = rawMessage ?? fallbackMessage;

    if (!rawMessage) {
      try {
        const serialized = JSON.stringify(error);
        if (typeof serialized === 'string') {
          message = serialized;
        }
      } catch {
        // keep fallback message
      }
    }

    const normalized = new Error(message);
    if (typeof record.name === 'string') {
      normalized.name = record.name;
    }

    for (const [key, value] of Object.entries(record)) {
      if (key === 'message' || key === 'name') continue;
      (normalized as Record<string, unknown>)[key] = value;
    }

    if ('status' in record && (normalized as Record<string, unknown>).status === undefined) {
      const status = (record as { status?: unknown }).status;
      if (status !== undefined) {
        (normalized as Record<string, unknown>).status = status;
      }
    }

    return normalized;
  }

  try {
    const serialized = JSON.stringify(error);
    return new Error(serialized === undefined ? fallbackMessage : serialized);
  } catch {
    return new Error(fallbackMessage);
  }
};
