#!/usr/bin/env node

import fs from 'node:fs';
import path from 'node:path';
import os from 'node:os';
import { mkdir, rename, cp, rm, stat } from 'node:fs/promises';

const LOG_PREFIX = '\u001b[36m[pipelines]\u001b[0m';

const normalizeBoolean = (value) =>
  value === true ||
  value === '1' ||
  value === 1 ||
  (typeof value === 'string' && value.toLowerCase() === 'true');

const defaultCacheRoot =
  process.env.PIPELINES_FULL_CACHE_ROOT ||
  path.join(os.homedir(), '.cache', 'ae-framework', 'pipelines');

const artifacts = [
  {
    label: 'verify-lite artifacts',
    source: path.resolve('artifacts/verify-lite'),
    cacheEnv: 'PIPELINES_FULL_VERIFY_LITE_CACHE',
    defaultDir: 'verify-lite',
  },
  {
    label: 'mutation reports',
    source: path.resolve('reports/mutation'),
    cacheEnv: 'PIPELINES_FULL_MUTATION_CACHE',
    defaultDir: 'mutation',
  },
];

async function ensureDir(dir) {
  await mkdir(dir, { recursive: true });
}

async function pathExists(target) {
  try {
    await stat(target);
    return true;
  } catch (error) {
    if (error.code === 'ENOENT') {
      return false;
    }
    throw error;
  }
}

async function moveWithFallback(source, destination) {
  try {
    await rename(source, destination);
  } catch (error) {
    if (error.code !== 'EXDEV') {
      throw error;
    }
    await cp(source, destination, { recursive: true });
    await rm(source, { recursive: true, force: true });
  }
}

async function uniqueDestination(cacheRoot) {
  const base = new Date().toISOString().replace(/[:.]/g, '-');
  for (let attempt = 0; attempt < 8; attempt++) {
    const suffix = attempt === 0 ? '' : `-${Math.random().toString(36).slice(2, 8)}`;
    const candidate = path.join(cacheRoot, `${base}${suffix}`);
    if (!(await pathExists(candidate))) {
      return candidate;
    }
  }
  return path.join(cacheRoot, `${base}-${process.pid}-${Date.now()}`);
}

async function relocateArtifact({ label, source, cacheEnv, defaultDir }) {
  if (!fs.existsSync(source)) {
    return null;
  }

  const cacheRoot = cacheEnv && process.env[cacheEnv]
    ? path.resolve(process.env[cacheEnv])
    : path.join(defaultCacheRoot, defaultDir);

  await ensureDir(cacheRoot);

  const destination = await uniqueDestination(cacheRoot);

  console.log(`${LOG_PREFIX} moving ${label} -> ${destination}`);
  await moveWithFallback(source, destination);

  return destination;
}

export async function cleanupArtifacts() {
  if (normalizeBoolean(process.env.PIPELINES_FULL_KEEP_ARTIFACTS)) {
    console.log(`${LOG_PREFIX} cleanup skipped (PIPELINES_FULL_KEEP_ARTIFACTS=1)`);
    return [];
  }

  await ensureDir(defaultCacheRoot);

  const results = [];
  for (const artifact of artifacts) {
    try {
      const destination = await relocateArtifact(artifact);
      if (destination) {
        results.push({ label: artifact.label, destination });
      }
    } catch (error) {
      console.warn(`${LOG_PREFIX} failed to relocate ${artifact.label}: ${error.message}`);
    }
  }

  if (results.length === 0) {
    console.log(`${LOG_PREFIX} cleanup complete (no artifacts relocated)`);
  } else {
    console.log(
      `${LOG_PREFIX} cleanup complete (${results
        .map((entry) => `${entry.label} → ${entry.destination}`)
        .join(', ')})`
    );
  }

  return results;
}

if (import.meta.url === `file://${process.argv[1]}`) {
  cleanupArtifacts().catch((error) => {
    console.error(`${LOG_PREFIX} cleanup failed: ${error.message}`);
    process.exitCode = 1;
  });
}
