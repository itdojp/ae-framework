#!/usr/bin/env node

import { mkdir, rm, cp, access, constants } from 'fs/promises';
import path from 'path';
import { fileURLToPath } from 'url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const repoRoot = path.resolve(__dirname, '..', '..');

const CACHE_ROOT = path.join(repoRoot, '.cache', 'test-results');
const BASELINE_ROOT = path.join(repoRoot, '.cache', 'test-results-baseline');

const TARGETS = [
  {
    source: path.join(repoRoot, 'reports', 'mutation'),
    cache: path.join(CACHE_ROOT, 'reports', 'mutation'),
    baseline: path.join(BASELINE_ROOT, 'reports', 'mutation'),
    label: 'Mutation quick reports',
  },
  {
    source: path.join(repoRoot, 'artifacts', 'mbt'),
    cache: path.join(CACHE_ROOT, 'artifacts', 'mbt'),
    baseline: path.join(BASELINE_ROOT, 'artifacts', 'mbt'),
    label: 'MBT summaries',
  },
  {
    source: path.join(repoRoot, 'artifacts', 'properties'),
    cache: path.join(CACHE_ROOT, 'artifacts', 'properties'),
    baseline: path.join(BASELINE_ROOT, 'artifacts', 'properties'),
    label: 'Property harness outputs',
  },
];

const MODES = new Set(['--store', '--restore', '--status', '--snapshot']);
const mode = process.argv.slice(2).find(arg => MODES.has(arg));

if (!mode) {
  console.error(
    'Usage: node scripts/pipelines/sync-test-results.mjs [--store|--restore|--status|--snapshot]',
  );
  process.exit(1);
}

async function pathExists(targetPath) {
  try {
    await access(targetPath, constants.F_OK);
    return true;
  } catch {
    return false;
  }
}

async function ensureParent(targetPath) {
  await mkdir(path.dirname(targetPath), { recursive: true });
}

async function copyRecursive(from, to) {
  await ensureParent(to);
  await rm(to, { recursive: true, force: true });
  await cp(from, to, { recursive: true });
}

async function handleStore() {
  await mkdir(CACHE_ROOT, { recursive: true });
  let copied = 0;
  for (const entry of TARGETS) {
    if (!(await pathExists(entry.source))) {
      console.log(`Skipping ${entry.label}: source missing (${entry.source})`);
      continue;
    }
    await copyRecursive(entry.source, entry.cache);
    console.log(`Stored ${entry.label} -> ${path.relative(repoRoot, entry.cache)}`);
    copied += 1;
  }
  if (copied === 0) {
    console.log('No test results were stored (sources missing).');
  }
}

async function handleRestore() {
  let restored = 0;
  for (const entry of TARGETS) {
    if (!(await pathExists(entry.cache))) {
      console.log(`Skipping ${entry.label}: cache missing (${entry.cache})`);
      continue;
    }
    await copyRecursive(entry.cache, entry.source);
    console.log(
      `Restored ${entry.label} -> ${path.relative(repoRoot, entry.source)}`,
    );
    restored += 1;
  }
  if (restored === 0) {
    console.log('No cached test results were restored.');
  }
}

async function handleSnapshot() {
  await mkdir(BASELINE_ROOT, { recursive: true });
  let snapshotted = 0;
  for (const entry of TARGETS) {
    if (!(await pathExists(entry.cache))) {
      console.log(`Skipping ${entry.label}: cache missing (${entry.cache})`);
      continue;
    }
    await copyRecursive(entry.cache, entry.baseline);
    console.log(
      `Snapshot ${entry.label} -> ${path.relative(repoRoot, entry.baseline)}`,
    );
    snapshotted += 1;
  }
  if (snapshotted === 0) {
    console.log('No cached test results were snapshotted.');
  }
}

async function handleStatus() {
  const status = await Promise.all(
    TARGETS.map(async entry => ({
      label: entry.label,
      sourceExists: await pathExists(entry.source),
      cacheExists: await pathExists(entry.cache),
      baselineExists: await pathExists(entry.baseline),
    })),
  );
  for (const entry of status) {
    console.log(
      `${entry.label}: source=${entry.sourceExists ? 'present' : 'missing'}, cache=${entry.cacheExists ? 'present' : 'missing'}, baseline=${entry.baselineExists ? 'present' : 'missing'}`,
    );
  }
}

try {
  if (mode === '--store') {
    await handleStore();
  } else if (mode === '--restore') {
    await handleRestore();
  } else if (mode === '--snapshot') {
    await handleSnapshot();
  } else {
    await handleStatus();
  }
} catch (error) {
  console.error('Failed to synchronise test results cache:', error);
  process.exit(1);
}
