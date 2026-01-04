export const stringifyUnknown = (value: unknown, fallback = '[unserializable]'): string => {
  if (value == null) return '';
  if (typeof value === 'string') return value;
  if (typeof value === 'number' || typeof value === 'boolean') return String(value);
  if (value instanceof Error) return value.message;
  try {
    const serialized = JSON.stringify(value);
    return typeof serialized === 'string' ? serialized : fallback;
  } catch {
    return fallback;
  }
};

export const hasConstructorProperty = <TKey extends string>(
  value: unknown,
  key: TKey
): value is Record<TKey, new (...args: unknown[]) => unknown> => {
  if (!value || typeof value !== 'object') {
    return false;
  }
  const candidate = (value as Record<string, unknown>)[key];
  return typeof candidate === 'function';
};
