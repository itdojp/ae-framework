import { glob } from 'glob';
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import path from 'node:path';
import crypto from 'node:crypto';

const OUT_DIR = 'artifacts/types';
const SNAP_DIR = 'api';
const SNAP_FILE = path.join(SNAP_DIR, 'public-types.d.ts');

const stripShebang = (content) => content.replace(/^#!.*(?:\r?\n)?/gm, '');

async function collect() {
  const files = (await glob(`${OUT_DIR}/**/*.d.ts`)).sort();
  let bundle = '';
  for (const f of files) {
    const rel = path.relative(OUT_DIR, f);
    const txt = stripShebang(await readFile(f, 'utf8'));
    bundle += `// ---- ${rel} ----\n${txt}\n`;
  }
  const hash = crypto.createHash('sha1').update(bundle).digest('hex');
  return { bundle, hash };
}

await mkdir(SNAP_DIR, { recursive: true });
const { bundle, hash } = await collect();
await writeFile(SNAP_FILE, `// snapshot sha1=${hash}\n${bundle}`);
console.log(`[api:snapshot] wrote ${SNAP_FILE} (${bundle.length} bytes, sha1=${hash})`);
