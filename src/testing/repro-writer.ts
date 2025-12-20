import { writeFile, mkdir } from 'node:fs/promises';

const JSON_UNSAFE_REGEX = /[<>\u2028\u2029/]/g;
const ESCAPED_LINE_SEPARATOR = '\\u2028';
const ESCAPED_PARAGRAPH_SEPARATOR = '\\u2029';

const JSON_UNSAFE_MAP: Record<string, string> = {
  '<': '\\u003C',
  '>': '\\u003E',
  '/': '\\u002F',
  '\u2028': ESCAPED_LINE_SEPARATOR,
  '\u2029': ESCAPED_PARAGRAPH_SEPARATOR,
};

function escapeJsonForCode(value: string): string {
  return value.replace(JSON_UNSAFE_REGEX, (char) => JSON_UNSAFE_MAP[char] ?? char);
}

function sanitizeFilename(str: string): string {
  return str.replace(/[^a-zA-Z0-9-_]/g, '_');
}

export async function writeRepro(name: string, seed: number, data: unknown) {
  await mkdir('artifacts/repros', { recursive: true });
  const testNameLiteral = escapeJsonForCode(JSON.stringify(`${name} repro`));
  const seedLiteral = escapeJsonForCode(JSON.stringify(String(seed)));
  const safeNameForFile = sanitizeFilename(name);
  const serializedData = escapeJsonForCode(JSON.stringify(JSON.stringify(data)));
  const body = `test(${testNameLiteral}, () => { process.env.AE_SEED=${seedLiteral}; const data = JSON.parse(${serializedData}); /* TODO: call SUT(data) */ });`;
  await writeFile(`artifacts/repros/${safeNameForFile}.repro.ts`, body);
}
