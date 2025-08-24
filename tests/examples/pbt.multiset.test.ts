import { test } from 'vitest';
import fc from 'fast-check';
import { aeAssert } from '../../src/testing/fc-assert';
import { expectMultisetEqual } from '../../src/testing/properties';

test('sort preserves multiset', () => {
  aeAssert(fc.property(fc.array(fc.integer()), (arr) => {
    const sorted = [...arr].sort((a,b)=>a-b);
    expectMultisetEqual(arr, sorted);
  }));
});