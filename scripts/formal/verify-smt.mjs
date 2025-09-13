#!/usr/bin/env node
// Stub runner for verify:smt
const solver = (process.argv.find(a => a.startsWith('--solver=')) || '').split('=')[1] || 'z3';
console.log(`verify:smt stub — solver=${solver} (integration TBD)`);
process.exit(0);

