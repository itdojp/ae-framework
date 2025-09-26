import { writeFile, mkdir } from 'node:fs/promises';

const CHAR_ESCAPE_MAP: Record<string, string> = {
  "'": "\\'",
  "\\": "\\\\",
  "\n": "\\n",
  "\r": "\\r",
  "\t": "\\t",
  "\f": "\\f",
  "\b": "\\b",
  "\u2028": "\\u2028",
  "\u2029": "\\u2029",
  "<": "\\u003C",
  ">": "\\u003E",
  "/": "\\u002F",
  "\0": "\\0",
};

const ESCAPE_REGEX = /['\\\n\r\t\f\b\u2028\u2029<>/\0]/g;

function escapeForSingleQuotedString(str: string): string {
  return str.replace(ESCAPE_REGEX, (char) => CHAR_ESCAPE_MAP[char] ?? char);
}

function sanitizeFilename(str: string): string {
  return str.replace(/[^a-zA-Z0-9-_]/g, '_');
}

export async function writeRepro(name: string, seed: number, data: unknown) {
  await mkdir('artifacts/repros', { recursive: true });
  const safeNameForCode = escapeForSingleQuotedString(name);
  const safeNameForFile = sanitizeFilename(name);
  const body = `test('${safeNameForCode} repro', () => { process.env.AE_SEED='${seed}'; const data=${JSON.stringify(data)}; /* TODO: call SUT(data) */ });`;
  await writeFile(`artifacts/repros/${safeNameForFile}.repro.ts`, body);
}
