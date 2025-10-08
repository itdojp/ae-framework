#!/usr/bin/env node

import { spawn } from 'child_process';

const args = process.argv.slice(2);
const dryRun = args.includes('--dry-run');
const specArgIndex = args.findIndex((arg) => arg === '--spec');
const specPath = specArgIndex >= 0 ? args[specArgIndex + 1] : undefined;

const command = ['pnpm', 'test:cli:fuzz'];
if (specPath) {
  command.push('--');
  command.push(specPath);
}

if (dryRun) {
  console.log('[api-fuzz] dry-run:', command.join(' '));
  process.exit(0);
}

const child = spawn(command[0], command.slice(1), { stdio: 'inherit' });
child.on('close', (code) => {
  process.exit(code ?? 1);
});
