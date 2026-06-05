import path from 'node:path';

export class CodeGenerationSafetyError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'CodeGenerationSafetyError';
  }
}

const RESERVED_TS_IDENTIFIERS = new Set([
  'arguments',
  'await',
  'break',
  'case',
  'catch',
  'class',
  'const',
  'continue',
  'debugger',
  'default',
  'delete',
  'do',
  'else',
  'enum',
  'eval',
  'export',
  'extends',
  'false',
  'finally',
  'for',
  'function',
  'if',
  'implements',
  'import',
  'in',
  'instanceof',
  'interface',
  'let',
  'new',
  'null',
  'package',
  'private',
  'protected',
  'public',
  'return',
  'static',
  'super',
  'switch',
  'this',
  'throw',
  'true',
  'try',
  'typeof',
  'undefined',
  'var',
  'void',
  'while',
  'with',
  'yield',
]);

const normalizeAsciiWords = (input: string): string[] =>
  String(input)
    .normalize('NFKD')
    .replace(/[\u0300-\u036f]/g, '')
    .split(/[^A-Za-z0-9]+/)
    .map((part) => part.trim())
    .filter(Boolean);

const capitalizeWord = (value: string): string =>
  value.length === 0 ? value : `${value.charAt(0).toUpperCase()}${value.slice(1)}`;

const ensureIdentifier = (candidate: string, fallback: string): string => {
  let identifier = candidate.replace(/[^A-Za-z0-9_$]/g, '');
  if (!identifier) {
    identifier = fallback;
  }
  if (!/^[A-Za-z_$]/.test(identifier)) {
    identifier = `${fallback}${identifier}`;
  }
  if (RESERVED_TS_IDENTIFIERS.has(identifier.toLowerCase())) {
    identifier = `${identifier}Generated`;
  }
  return identifier;
};

export function toSafeFileSlug(input: string, fallback = 'generated'): string {
  const slug = normalizeAsciiWords(input).join('-').toLowerCase();
  return slug || fallback;
}

export function toSafeIdentifier(input: string, fallback = 'generatedIdentifier'): string {
  const words = normalizeAsciiWords(input);
  const [first, ...rest] = words;
  const candidate = first
    ? `${first.charAt(0).toLowerCase()}${first.slice(1)}${rest.map(capitalizeWord).join('')}`
    : fallback;
  return ensureIdentifier(candidate, fallback);
}

export function toSafePascalIdentifier(input: string, fallback = 'GeneratedIdentifier'): string {
  const words = normalizeAsciiWords(input);
  const candidate = words.length > 0 ? words.map(capitalizeWord).join('') : fallback;
  return ensureIdentifier(candidate, fallback);
}

export function toTsStringLiteral(input: string): string {
  return JSON.stringify(String(input));
}

export function toSafeLineCommentText(input: string | undefined, fallback = 'N/A'): string {
  const normalized = String(input ?? '')
    .replace(/\r\n?/g, '\n')
    .replace(/[\u0000-\u001F\u007F]/g, ' ')
    .replace(/\*\//g, '*\\/');
  const singleLine = normalized
    .split('\n')
    .map((part) => part.trim())
    .filter(Boolean)
    .join(' | ');
  return singleLine || fallback;
}

export function assertSafeRelativePath(input: string, label = 'generated path'): string {
  const raw = String(input).trim();
  if (!raw) {
    throw new CodeGenerationSafetyError(`${label} must be non-empty`);
  }
  if (raw.includes('\0')) {
    throw new CodeGenerationSafetyError(`${label} must not contain NUL bytes`);
  }
  if (raw.includes('\\')) {
    throw new CodeGenerationSafetyError(`${label} must use POSIX-style '/' separators`);
  }
  if (raw.startsWith('//') || path.posix.isAbsolute(raw) || path.isAbsolute(raw) || /^[A-Za-z]:[\\/]/.test(raw)) {
    throw new CodeGenerationSafetyError(`${label} must be workspace-relative`);
  }

  const segments = raw.split('/').filter((segment) => segment.length > 0);
  if (segments.some((segment) => segment === '.' || segment === '..')) {
    throw new CodeGenerationSafetyError(`${label} must not contain dot-segment path components`);
  }
  if (segments.some((segment) => segment.toLowerCase() === '.git')) {
    throw new CodeGenerationSafetyError(`${label} must not target Git metadata directories`);
  }
  return path.posix.join(...segments);
}

export function buildSafeRelativePath(root: string, filename: string, label = 'generated path'): string {
  const safeRoot = String(root).trim() === ''
    ? ''
    : String(root).trim() === '.'
      ? ''
      : assertSafeRelativePath(root, `${label} root`);
  const safeFilename = assertSafeRelativePath(filename, `${label} filename`);
  const joined = safeRoot ? path.posix.join(safeRoot, safeFilename) : safeFilename;
  return assertSafeRelativePath(joined, label);
}
