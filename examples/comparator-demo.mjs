#!/usr/bin/env node
// Simple comparator demo: parse two coverage threshold objects and print strictest

const A = { lines: 85, functions: 85, branches: 80, statements: 85 };
const B = { lines: 90, functions: 88, branches: 82, statements: 90 };

function strictestCoverage(a, b) {
  const keys = ['lines', 'functions', 'branches', 'statements'];
  const out = {};
  for (const k of keys) {
    const av = Number(a?.[k] ?? 0);
    const bv = Number(b?.[k] ?? 0);
    out[k] = Math.max(av, bv); // higher is stricter for coverage
  }
  return out;
}

const strictest = strictestCoverage(A, B);
console.log('A =', A);
console.log('B =', B);
console.log('strictest =', strictest);

