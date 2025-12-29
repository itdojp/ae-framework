import { readFile, writeFile } from 'node:fs/promises';
import { spawn } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import path from 'node:path';

const stripShebang = (content) => content.replace(/^#!.*(?:\r?\n)?/gm, '');

function run(cmd, args) {
  return new Promise((res) => {
    const p = spawn(cmd, args, { stdio: 'inherit' });
    p.on('close', (code) => res(code));
  });
}

// 1) emit d.ts
const code = await run('tsc', ['-p', 'tsconfig.types.json']);
if (code !== 0) process.exit(code);

// 2) 生成されたバンドルを一時ファイルへ
const snap = await readFile('api/public-types.d.ts', 'utf8').catch(()=> '');
const { glob } = await import('glob');
import { readFile as rf } from 'node:fs/promises';
const files = (await glob('artifacts/types/**/*.d.ts')).sort();
let current = '';
for (const f of files) {
  const rel = path.relative('artifacts/types', f);
  const txt = stripShebang(await rf(f, 'utf8'));
  current += `// ---- ${rel} ----\n${txt}\n`;
}

await writeFile('artifacts/public-types.current.d.ts', current);

// 3) 簡易 diff（存在しなければ「初回」扱い）
if (!snap) {
  console.log('[api:check] no baseline (first run). Use `pnpm api:update` to create snapshot.');
  process.exit(0);
}

// Remove hash line from snapshot for comparison
const snapContent = stripShebang(snap.replace(/^\/\/ snapshot sha1=.*\n/, ''));
const isSame = snapContent.replace(/\r\n/g,'\n') === current.replace(/\r\n/g,'\n');
if (!isSame) {
  console.log('[api:check] type snapshot changed. Run `pnpm api:update` to accept.');
  // ここでは非ブロッキング（exit 0）。ゲート化は後続PRで。
}
