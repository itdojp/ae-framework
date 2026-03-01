#!/usr/bin/env node
import { execFileSync } from 'node:child_process';
import { mkdtempSync, rmSync, copyFileSync, mkdirSync } from 'node:fs';
import os from 'node:os';
import path from 'node:path';

const PNPM_BIN = process.platform === 'win32' ? 'pnpm.cmd' : 'pnpm';
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

const TYPESCRIPT_OPTIONS = [
  '--declaration',
  '--emitDeclarationOnly',
  '--declarationMap',
  'false',
  '--target',
  'es2022',
  '--module',
  'esnext',
  '--moduleResolution',
  'bundler',
  '--skipLibCheck',
  '--allowJs',
  '--esModuleInterop',
  '--allowSyntheticDefaultImports',
  '--verbatimModuleSyntax',
  'false',
];

const tempDir = mkdtempSync(path.join(os.tmpdir(), 'ae-public-types-sync-'));

try {
  execFileSync(
    PNPM_BIN,
    ['exec', 'tsc', ...TYPESCRIPT_OPTIONS, '--outDir', tempDir, ...TARGETS.map((target) => target.source)],
    { stdio: 'inherit' }
  );

  for (const target of TARGETS) {
    const compiledRelativePath = target.source
      .replace(/^src\//, '')
      .replace(/\.tsx?$/, '.d.ts')
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
