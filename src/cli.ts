#!/usr/bin/env node
import { main } from './runner/main.js';

main().catch((e) => { 
  console.error('[ae] fatal:', e); 
  process.exit(1); 
});