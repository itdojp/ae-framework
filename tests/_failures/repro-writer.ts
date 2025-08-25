import { writeFile, mkdir } from 'node:fs/promises';

// Helper to escape single quotes and backslashes for JS string literals
function escapeForSingleQuotedString(str: string): string {
  return str.replace(/\\/g, '\\\\').replace(/'/g, "\\'");
}

// Helper to sanitize filename (alphanumeric, dash, underscore only)
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