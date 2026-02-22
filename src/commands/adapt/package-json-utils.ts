type PackageJsonObject = {
  scripts?: Record<string, string>;
  [key: string]: unknown;
};

export const normalizeScriptRecord = (value: unknown): Record<string, string> | undefined => {
  if (!value || typeof value !== 'object' || Array.isArray(value)) {
    return undefined;
  }

  const normalized: Record<string, string> = {};
  for (const [entryKey, entryValue] of Object.entries(value as Record<string, unknown>)) {
    if (typeof entryValue === 'string') {
      normalized[entryKey] = entryValue;
    }
  }

  return normalized;
};

export const parsePackageJsonWithNormalizedScripts = <T extends PackageJsonObject>(raw: string): T => {
  const parsed: unknown = JSON.parse(raw);
  if (!parsed || typeof parsed !== 'object' || Array.isArray(parsed)) {
    return {} as T;
  }

  const source = parsed as Record<string, unknown>;
  const normalized: Record<string, unknown> = { ...source };

  if ('scripts' in source) {
    const normalizedScripts = normalizeScriptRecord(source['scripts']);
    if (normalizedScripts !== undefined) {
      normalized['scripts'] = normalizedScripts;
    } else {
      delete normalized['scripts'];
    }
  }

  return normalized as T;
};
