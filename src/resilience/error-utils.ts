export const normalizeError = (error: unknown, fallbackMessage: string): Error => {
  if (error instanceof Error) return error;
  if (typeof error === 'string') return new Error(error);

  if (error && typeof error === 'object') {
    const record = error as Record<string, unknown>;
    const rawMessage = typeof record['message'] === 'string' ? record['message'] : null;
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
    if (typeof record['name'] === 'string') {
      normalized.name = record['name'];
    }

    const normalizedRecord = normalized as unknown as Record<string, unknown>;
    for (const [key, value] of Object.entries(record)) {
      if (key === 'message' || key === 'name') continue;
      normalizedRecord[key] = value;
    }

    if ('status' in record && normalizedRecord['status'] === undefined) {
      const status = record['status'];
      if (status !== undefined) {
        normalizedRecord['status'] = status;
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
