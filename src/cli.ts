#!/usr/bin/env node
/**
 * Legacy compatibility shim.
 *
 * Canonical main CLI entrypoint in this repository is `src/cli/index.ts`.
 * Benchmark/report compatibility flows that still rely on the legacy `cac`
 * router continue to enter through this file until they are migrated.
 */
import { main } from './runner/main.js';
import { safeExit } from './utils/safe-exit.js';

main().catch((e) => { 
  console.error('[ae] fatal:', e); 
  safeExit(1); 
});
