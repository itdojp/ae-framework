#!/usr/bin/env node
// Stub runner for verify:smt
const solverArg = process.argv.find(a => a.startsWith('--solver='));
const solver = solverArg ? solverArg.slice('--solver='.length) : 'z3';
console.log(`verify:smt stub — solver=${solver || 'z3'} (integration TBD)`);
process.exit(0);
