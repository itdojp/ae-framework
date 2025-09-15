#!/usr/bin/env node
import { main } from './runner/main.js';
import { safeExit } from './utils/safe-exit.js';

main().catch((e) => { 
  console.error('[ae] fatal:', e); 
  safeExit(1); 
});
