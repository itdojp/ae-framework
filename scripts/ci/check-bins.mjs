#!/usr/bin/env node
// Bin smoke check: verifies that all package.json#bin paths exist and are executable.
// Also attempts a harmless execution with --help to catch spawn-time errors.

import fs from 'fs';
import path from 'path';
import { spawnSync } from 'child_process';

function fail(msg) {
  console.error(`❌ ${msg}`);
  process.exitCode = 1;
}

try {
  const root = process.cwd();
  const pkg = JSON.parse(fs.readFileSync(path.join(root, 'package.json'), 'utf8'));
  const binMap = pkg.bin || {};

  const entries = Object.entries(binMap);
  if (entries.length === 0) {
    console.log('ℹ️  No bin entries defined in package.json');
    process.exit(0);
  }

  console.log('🔎 Checking bin entries:');
  for (const [name, rel] of entries) {
    const binPath = path.resolve(root, rel);

    // Existence
    try {
      fs.accessSync(binPath, fs.constants.F_OK);
    } catch (e) {
      fail(`Bin not found for ${name}: ${rel} (resolved: ${binPath})`);
      continue;
    }

    // Executable (POSIX only)
    if (process.platform !== 'win32') {
      try {
        fs.accessSync(binPath, fs.constants.X_OK);
      } catch (e) {
        fail(`Bin not executable for ${name}: ${rel} (chmod +x needed)`);
      }
    }

    // Harmless execution
    const res = spawnSync(process.execPath, [binPath, '--help'], {
      stdio: 'pipe',
      encoding: 'utf8',
      timeout: 8000,
    });
    if (res.error) {
      fail(`Failed to spawn ${name} (${rel}): ${res.error.message}`);
      continue;
    }
    // Non-zero exit code is tolerated; we only care spawn is possible.
    console.log(`✅ ${name}: ${rel} (exit=${res.status})`);
  }

  if (process.exitCode) {
    console.error('❌ Bin smoke check failed');
  } else {
    console.log('🎉 Bin smoke check passed');
  }
} catch (err) {
  fail(`Unexpected error: ${err instanceof Error ? err.message : String(err)}`);
}

