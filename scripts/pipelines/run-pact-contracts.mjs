#!/usr/bin/env node

import { spawn } from 'child_process';
import { readdirSync, existsSync } from 'node:fs';
import { join, basename } from 'node:path';

const args = process.argv.slice(2);
const dryRun = args.includes('--dry-run');
const contractArg = args.find((arg) => arg.startsWith('--contract='));
const env = { ...process.env };

if (contractArg) {
  env.PACT_CONTRACTS = contractArg.split('=')[1];
} else {
  const contractsDir = join(process.cwd(), 'contracts');
  if (existsSync(contractsDir)) {
    const contractFiles = readdirSync(contractsDir)
      .filter((file) => file.endsWith('.json'))
      .map((file) => basename(file));
    if (contractFiles.length > 0) {
      env.PACT_CONTRACTS = contractFiles.join(',');
    }
  }
}

const command = ['pnpm', 'test:contracts'];

if (dryRun) {
  console.log('[pact] dry-run:', command.join(' '));
  if (env.PACT_CONTRACTS) {
    console.log('[pact]   with PACT_CONTRACTS=%s', env.PACT_CONTRACTS);
  }
  process.exit(0);
}

const child = spawn(command[0], command.slice(1), {
  stdio: 'inherit',
  env,
});

child.on('close', (code) => {
  process.exit(code == null ? 1 : code);
});
