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

const hasTextField = (value: unknown): value is { text: string } => {
  if (!value || typeof value !== 'object') {
    return false;
  }
  const text = (value as { text?: unknown }).text;
  return typeof text === 'string';
};

export const extractAnthropicText = (content: unknown): string => {
  if (Array.isArray(content)) {
    for (const entry of content) {
      const text = extractAnthropicText(entry);
      if (text) return text;
    }
    return '';
  }
  if (hasTextField(content)) {
    return content.text;
  }
  if (typeof content === 'string') {
    return content;
  }
  return '';
};

const hasTextMethod = (value: unknown): value is { text: () => string } => {
  if (!value || typeof value !== 'object') {
    return false;
  }
  return typeof (value as { text?: unknown }).text === 'function';
};

export const extractGeminiText = (response: unknown): string => {
  if (hasTextMethod(response)) {
    const text = response.text();
    return typeof text === 'string' ? text : String(text);
  }
  if (response && typeof response === 'object') {
    const candidates = (response as { candidates?: unknown }).candidates;
    if (Array.isArray(candidates) && candidates.length > 0) {
      const first = candidates[0];
      if (first && typeof first === 'object') {
        const content = (first as { content?: unknown }).content;
        if (content && typeof content === 'object') {
          const parts = (content as { parts?: unknown }).parts;
          if (Array.isArray(parts) && parts.length > 0) {
            const part = parts[0];
            if (part && typeof part === 'object') {
              const text = (part as { text?: unknown }).text;
              return typeof text === 'string' ? text : '';
            }
          }
        }
      }
    }
  }
  return '';
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
