import { writeFile, mkdir } from 'node:fs/promises';

function sanitizeFilename(str: string): string {
  return str.replace(/[^a-zA-Z0-9-_]/g, '_');
}

export async function writeRepro(name: string, seed: number, data: unknown) {
  await mkdir('artifacts/repros', { recursive: true });
  const testNameLiteral = JSON.stringify(`${name} repro`);
  const seedLiteral = JSON.stringify(String(seed));
  const safeNameForFile = sanitizeFilename(name);
  const serializedData = JSON.stringify(JSON.stringify(data));
  const body = `test(${testNameLiteral}, () => { process.env.AE_SEED=${seedLiteral}; const data = JSON.parse(${serializedData}); /* TODO: call SUT(data) */ });`;
  await writeFile(`artifacts/repros/${safeNameForFile}.repro.ts`, body);
}
