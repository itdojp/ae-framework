#!/usr/bin/env node
import { readFileSync, readdirSync, statSync } from 'node:fs';
import path from 'node:path';
import process from 'node:process';

const packageRoot = path.resolve(import.meta.dirname, '..');
const sourceRoot = path.join(packageRoot, 'src');
const forbidden = /(?:from\s+['"]|import\s*\(\s*['"])(?:\.\.\/){2,}src\//;

function collectFiles(dir) {
  const entries = readdirSync(dir, { withFileTypes: true });
  const files = [];
  for (const entry of entries) {
    const target = path.join(dir, entry.name);
    if (entry.isDirectory()) {
      files.push(...collectFiles(target));
      continue;
    }
    if (entry.isFile() && /\.[cm]?tsx?$/u.test(entry.name)) {
      files.push(target);
    }
  }
  return files;
}

if (!statSync(sourceRoot).isDirectory()) {
  throw new Error(`Source root is not a directory: ${sourceRoot}`);
}

const violations = collectFiles(sourceRoot).filter((file) => forbidden.test(readFileSync(file, 'utf8')));
if (violations.length > 0) {
  process.stderr.write('packages/core must not import from repository root src/**:\n');
  for (const violation of violations) {
    process.stderr.write(`- ${path.relative(packageRoot, violation)}\n`);
  }
  process.exit(1);
}

process.stdout.write(`No root src/** imports found in ${path.relative(process.cwd(), sourceRoot)}\n`);
