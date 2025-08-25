// scripts/codemods/ts-ignore-to-expect.mjs
import { readFile, writeFile } from 'node:fs/promises';
import { glob } from 'glob';

const files = await glob('src/**/*.ts');
let totalChanges = 0;
let filesChanged = 0;

for (const f of files) {
  let t = await readFile(f, 'utf8');
  const before = t;
  t = t.replace(/\/\/\s*@ts-ignore\b/g, '// @ts-expect-error -- TODO: describe why');
  if (t !== before) {
    await writeFile(f, t);
    const changes = (before.match(/\/\/\s*@ts-ignore\b/g) || []).length;
    console.log(`[codemod] ${f}: replaced ${changes} ts-ignore occurrences`);
    totalChanges += changes;
    filesChanged++;
  }
}

console.log(`[codemod] replaced ts-ignore -> ts-expect-error (with TODO)`);
console.log(`[codemod] Total: ${totalChanges} replacements in ${filesChanged} files`);