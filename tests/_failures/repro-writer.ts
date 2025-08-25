import { writeFile, mkdir } from 'node:fs/promises';

export async function writeRepro(name: string, seed: number, data: unknown) {
  await mkdir('artifacts/repros', { recursive: true });
  const body = `test('${name} repro', () => { process.env.AE_SEED='${seed}'; const data=${JSON.stringify(data)}; /* TODO: call SUT(data) */ });`;
  await writeFile(`artifacts/repros/${name}.repro.ts`, body);
}