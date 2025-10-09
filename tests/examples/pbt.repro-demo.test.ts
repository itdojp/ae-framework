import { test, expect } from 'vitest';
import fc from 'fast-check';
import { aeAssertRepro } from '../../src/testing/fc-assert.js';
import { expectMultisetEqual } from '../../src/testing/properties.js';

test('sort preserves multiset (with repro)', () => {
  aeAssertRepro('sort_multiset', fc.property(fc.array(fc.integer()), (arr) => {
    const sorted = [...arr].sort((a, b) => a - b);
    
    // This should pass - just checking multiset equality
    expectMultisetEqual(sorted, arr);
    
    // Ensure sorting preserves length
    expect(sorted.length).toBe(arr.length);
  }));
});

test('string reverse property (with repro)', () => {
  aeAssertRepro('string_reverse', fc.property(fc.string(), (str) => {
    const reversed = str.split('').reverse().join('');
    const doubleReversed = reversed.split('').reverse().join('');
    
    // This should always pass
    expect(doubleReversed).toBe(str);
    
    // Length should remain unchanged after reversing twice
    expect(doubleReversed.length).toBe(str.length);
  }));
});
