export const normalizeError = (error: unknown, fallbackMessage: string): Error => {
  if (error instanceof Error) return error;
  if (typeof error === 'string') return new Error(error);
  try {
    const serialized = JSON.stringify(error);
    return new Error(serialized === undefined ? fallbackMessage : serialized);
  } catch {
    return new Error(fallbackMessage);
  }
};
