#!/usr/bin/env node
import { execSync } from 'child_process';
try {
  const out = execSync('apalache-mc version', { stdio: ['ignore','pipe','pipe'] }).toString();
  console.log('✅ Apalache detected');
  console.log(out.trim());
  process.exit(0);
} catch (e) {
  console.warn('⚠️ Apalache not found in PATH');
  process.exit(0); // non-blocking
}
