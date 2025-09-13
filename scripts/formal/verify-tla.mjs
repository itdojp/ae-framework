#!/usr/bin/env node
// Stub runner for verify:tla
const engine = process.argv.includes('--engine=apalache') ? 'apalache' : 'tlc';
console.log(`verify:tla stub — engine=${engine} (integration TBD)`);
process.exit(0);

