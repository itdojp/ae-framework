export const REDACTED_VALUE = '[REDACTED]';

const SENSITIVE_KEY_PATTERN = /(?:^key$|authorization|cookie|set-cookie|password|passwd|passphrase|secret|token|api[_-]?key|apikey|access[_-]?key|private[_-]?key|public[_-]?key|ssh[_-]?key|signing[_-]?key|encryption[_-]?key|decryption[_-]?key|client[_-]?secret|session(?:id)?|jwt|dsn|database[_-]?url|connection[_-]?string|credential|refresh[_-]?token|id[_-]?token|sig(?:nature)?)/i;

const STRING_REDACTIONS: Array<[RegExp, string]> = [
  [/\bBearer\s+[A-Za-z0-9._~+/=-]+/gi, 'Bearer [REDACTED]'],
  [/\bBasic\s+[A-Za-z0-9+/=-]+/gi, 'Basic [REDACTED]'],
  [
    /([?&](?:access[_-]?token|api[_-]?key|apikey|authorization|client[_-]?secret|code|cookie|database[_-]?url|dsn|id[_-]?token|jwt|key|password|refresh[_-]?token|secret|session(?:id)?|sig(?:nature)?|token)=)([^&#\s]+)/gi,
    '$1[REDACTED]',
  ],
  [
    /\b(access[_-]?token|api[_-]?key|apikey|authorization|client[_-]?secret|cookie|database[_-]?url|dsn|id[_-]?token|jwt|key|password|refresh[_-]?token|secret|session(?:id)?|sig(?:nature)?|token)=([^&\s]+)/gi,
    '$1=[REDACTED]',
  ],
  [/\b((?:postgres(?:ql)?|mysql|mongodb(?:\+srv)?|redis|amqp|https?):\/\/)([^:@/\s]+):([^@/\s]+)@/gi, '$1[REDACTED]@'],
  [/\b(Cookie:\s*)[^\r\n]+/gi, '$1[REDACTED]'],
  [/\b(Set-Cookie:\s*)[^\r\n]+/gi, '$1[REDACTED]'],
];

export function isSensitiveKey(key: string): boolean {
  return SENSITIVE_KEY_PATTERN.test(key);
}

export function redactSensitiveString(value: string): string {
  return STRING_REDACTIONS.reduce((current, [pattern, replacement]) => current.replace(pattern, replacement), value);
}

export function redactSensitiveData(value: unknown, seen = new WeakSet<object>()): unknown {
  if (typeof value === 'string') {
    return redactSensitiveString(value);
  }
  if (value === null || typeof value !== 'object') {
    return value;
  }
  if (seen.has(value)) {
    return '[Circular]';
  }
  seen.add(value);

  if (Array.isArray(value)) {
    return value.map((entry) => redactSensitiveData(entry, seen));
  }

  const redacted: Record<string, unknown> = {};
  for (const [key, nested] of Object.entries(value as Record<string, unknown>)) {
    redacted[key] = isSensitiveKey(key) ? REDACTED_VALUE : redactSensitiveData(nested, seen);
  }
  return redacted;
}

export function safeJsonForLogging(value: unknown): unknown {
  try {
    return redactSensitiveData(value);
  } catch {
    return '[Unserializable payload]';
  }
}

export function safeUrlPath(value: string | undefined): string {
  if (!value) return '/';
  try {
    const parsed = new URL(value, 'http://local.invalid');
    return parsed.pathname || '/';
  } catch {
    return value.split('?')[0] || '/';
  }
}

export function safeErrorForLogging(error: unknown): unknown {
  if (error instanceof Error) {
    return {
      name: error.name,
      message: redactSensitiveString(error.message),
    };
  }
  return redactSensitiveData(error);
}

export function safeStringForCassette(value: string): string {
  return redactSensitiveString(value);
}

export type SafeTelemetryAttributeValue = string | number | boolean;

export function sanitizeTelemetryAttributes(
  attributes: Record<string, unknown> | undefined,
): Record<string, SafeTelemetryAttributeValue> | undefined {
  if (attributes === undefined) {
    return undefined;
  }

  const safeAttributes: Record<string, SafeTelemetryAttributeValue> = {};
  for (const [key, value] of Object.entries(attributes)) {
    if (value === undefined || value === null) {
      continue;
    }
    if (isSensitiveKey(key)) {
      safeAttributes[key] = REDACTED_VALUE;
      continue;
    }
    if (typeof value === 'string') {
      safeAttributes[key] = redactSensitiveString(value);
      continue;
    }
    if (typeof value === 'number' || typeof value === 'boolean') {
      safeAttributes[key] = value;
      continue;
    }
    try {
      safeAttributes[key] = JSON.stringify(redactSensitiveData(value));
    } catch {
      safeAttributes[key] = '[Unserializable payload]';
    }
  }

  return safeAttributes;
}
