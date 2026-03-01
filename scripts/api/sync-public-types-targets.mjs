#!/usr/bin/env node
import { execFileSync } from 'node:child_process';
import { mkdtempSync, rmSync, copyFileSync, mkdirSync } from 'node:fs';
import os from 'node:os';
import path from 'node:path';

const PNPM_BIN = process.platform === 'win32' ? 'pnpm.cmd' : 'pnpm';
const TYPESCRIPT_PROJECT_PATH = path.resolve('configs/tsconfig/tsconfig.public-types-sync.json');
const TARGETS = [
  {
    source: 'src/agents/adapters/ui-ux-agent-adapter.ts',
    targetDts: 'artifacts/types/src/agents/adapters/ui-ux-agent-adapter.d.ts',
  },
  {
    source: 'src/utils/enhanced-state-manager.ts',
    targetDts: 'artifacts/types/src/utils/enhanced-state-manager.d.ts',
  },
];

const tempDir = mkdtempSync(path.join(os.tmpdir(), 'ae-public-types-sync-'));

try {
  execFileSync(
    PNPM_BIN,
    [
      'exec',
      'tsc',
      '-p',
      TYPESCRIPT_PROJECT_PATH,
      '--declaration',
      '--emitDeclarationOnly',
      '--declarationMap',
      'false',
      '--outDir',
      tempDir,
    ],
    { stdio: 'inherit' }
  );

  for (const target of TARGETS) {
    const compiledRelativePath = target.targetDts
      .replace(/^artifacts\/types\//, '')
      .split(path.posix.sep)
      .join(path.sep);
    const compiledPath = path.join(tempDir, compiledRelativePath);
    const destinationPath = path.resolve(target.targetDts);
    mkdirSync(path.dirname(destinationPath), { recursive: true });
    copyFileSync(compiledPath, destinationPath);
    console.log(`[api:sync-targets] synced ${target.targetDts}`);
  }
} finally {
  rmSync(tempDir, { recursive: true, force: true });
}
