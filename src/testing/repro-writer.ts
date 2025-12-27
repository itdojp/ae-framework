import { writeFile, mkdir } from 'node:fs/promises';
import { join } from 'node:path';

const JSON_UNSAFE_REGEX = /[<>\u2028\u2029/]/g;
const ESCAPED_LINE_SEPARATOR = '\\u2028';
const ESCAPED_PARAGRAPH_SEPARATOR = '\\u2029';
const REPRO_DIR = 'artifacts/repros';

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
  await mkdir(REPRO_DIR, { recursive: true });
  const testNameLiteral = escapeJsonForCode(JSON.stringify(`${name} repro`));
  const seedLiteral = escapeJsonForCode(JSON.stringify(String(seed)));
  const safeNameForFile = sanitizeFilename(name) || 'repro';
  const jsonPath = join(REPRO_DIR, `${safeNameForFile}.repro.json`);
  const tsPath = join(REPRO_DIR, `${safeNameForFile}.repro.ts`);
  const jsonPayload = escapeJsonForCode(JSON.stringify(data, null, 2));
  const dataPathLiteral = escapeJsonForCode(JSON.stringify(jsonPath));

  await writeFile(jsonPath, jsonPayload);

  const body = [
    "import { readFileSync } from 'node:fs';",
    `test(${testNameLiteral}, () => { process.env.AE_SEED=${seedLiteral}; const data = JSON.parse(readFileSync(${dataPathLiteral}, 'utf8')); /* TODO: call SUT(data) */ });`,
  ].join('\n');

  await writeFile(tsPath, body);
}
