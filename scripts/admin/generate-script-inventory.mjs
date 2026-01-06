import {
  accessSync,
  constants,
  existsSync,
  readFileSync,
  statSync,
  writeFileSync,
} from 'node:fs';
import { dirname, resolve } from 'node:path';

const args = process.argv.slice(2);
const outputPath = args[0] ? resolve(args[0]) : null;
const now = new Date().toISOString().slice(0, 10);

const findPackageJson = (startDir = process.cwd()) => {
  let dir = startDir;
  while (true) {
    const candidate = resolve(dir, 'package.json');
    if (existsSync(candidate)) {
      return candidate;
    }
    const parent = dirname(dir);
    if (parent === dir) {
      break;
    }
    dir = parent;
  }
  throw new Error(`Could not find package.json starting from ${startDir}`);
};

if (outputPath) {
  try {
    const stats = statSync(outputPath);
    if (stats.isDirectory()) {
      console.error(`Error: output path "${outputPath}" is a directory.`);
      process.exit(1);
    }
  } catch (error) {
    if (error?.code !== 'ENOENT') {
      throw error;
    }
    const dir = dirname(outputPath);
    try {
      accessSync(dir, constants.W_OK);
    } catch {
      console.error(`Error: cannot write to directory "${dir}".`);
      process.exit(1);
    }
  }
}

let pkg;
try {
  const pkgPath = findPackageJson();
  pkg = JSON.parse(readFileSync(pkgPath, 'utf8'));
} catch (error) {
  const message =
    error instanceof Error ? error.message : String(error ?? 'unknown error');
  console.error(`Failed to load package.json: ${message}`);
  process.exit(1);
}

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
  try {
    writeFileSync(outputPath, output);
  } catch (error) {
    const message =
      error instanceof Error ? error.message : String(error ?? 'unknown error');
    console.error(`Failed to write script inventory to "${outputPath}": ${message}`);
    process.exit(1);
  }
} else {
  process.stdout.write(output);
}
