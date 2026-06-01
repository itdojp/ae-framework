export const SAFE_TYPESCRIPT_IDENTIFIER_MAX_LENGTH = 80;

const safeTypeScriptIdentifierPattern = /^[A-Za-z_][A-Za-z0-9_]*$/;

const reservedTypeScriptIdentifiers = new Set([
  'break', 'case', 'catch', 'class', 'const', 'continue', 'debugger', 'default', 'delete', 'do',
  'else', 'export', 'extends', 'finally', 'for', 'function', 'if', 'import', 'in', 'instanceof',
  'new', 'return', 'super', 'switch', 'this', 'throw', 'try', 'typeof', 'var', 'void', 'while',
  'with', 'yield', 'let', 'static', 'enum', 'await', 'implements', 'package', 'protected',
  'interface', 'private', 'public', 'eval', 'arguments',
]);

export function getTypeScriptIdentifierPolicyError(value: string): string | null {
  if (value.length === 0) return 'must be a non-empty TypeScript identifier';
  if (value.length > SAFE_TYPESCRIPT_IDENTIFIER_MAX_LENGTH) {
    return `must be at most ${SAFE_TYPESCRIPT_IDENTIFIER_MAX_LENGTH} characters`;
  }
  if (!safeTypeScriptIdentifierPattern.test(value)) return 'must be a safe TypeScript identifier';
  if (reservedTypeScriptIdentifiers.has(value)) return 'must not be a reserved TypeScript keyword';
  return null;
}

export function assertSafeTypeScriptIdentifier(value: string, label: string): string {
  const error = getTypeScriptIdentifierPolicyError(value);
  if (error) {
    throw new Error(`Invalid ${label}: ${JSON.stringify(value)} (${error})`);
  }
  return value;
}
