import { readFileSync, writeFileSync } from 'node:fs';
import { resolve } from 'node:path';

const args = process.argv.slice(2);
const outputPath = args[0] ? resolve(args[0]) : null;
const now = new Date().toISOString().slice(0, 10);

const pkg = JSON.parse(readFileSync('package.json', 'utf8'));
const scripts = pkg.scripts ?? {};
const counts = new Map();
const rootScripts = [];

for (const name of Object.keys(scripts).sort()) {
  if (name.includes(':')) {
    const prefix = name.split(':')[0];
    counts.set(prefix, (counts.get(prefix) ?? 0) + 1);
  } else {
    counts.set('(root)', (counts.get('(root)') ?? 0) + 1);
    rootScripts.push(name);
  }
}

const total = Object.keys(scripts).length;
const entries = [...counts.entries()].sort((a, b) => {
  if (b[1] !== a[1]) {
    return b[1] - a[1];
  }
  return a[0].localeCompare(b[0]);
});

const lines = [];
lines.push(`# Issue #1006: Script Inventory (${now})`);
lines.push('');
lines.push('## 概要');
lines.push('- 対象: `package.json` の `scripts`');
lines.push('- 集計方法: `:` の前半プレフィックスで分類（例: `test:ci` → `test`）');
lines.push(`- 総数: ${total}`);
lines.push('');
lines.push('## プレフィックス別の件数');
lines.push('| prefix | count |');
lines.push('| --- | ---: |');
for (const [prefix, count] of entries) {
  lines.push(`| ${prefix} | ${count} |`);
}
lines.push('');
lines.push('## (root) scripts 一覧');
for (const name of rootScripts) {
  lines.push(`- ${name}`);
}
lines.push('');
lines.push('## 再生成');
lines.push('```bash');
lines.push('node scripts/admin/generate-script-inventory.mjs docs/notes/issue-1006-script-inventory.md');
lines.push('```');
lines.push('');
lines.push('## メモ');
lines.push('- `test`/`quality`/`verify`/`flake`/`security` で過半を占めるため、Phase 1 の統合対象候補。');
lines.push('- `(root)` は移行後にカテゴリへ再配置する前提で精査が必要。');
lines.push('');

const output = lines.join('\n');

if (outputPath) {
  writeFileSync(outputPath, output);
} else {
  process.stdout.write(output);
}
