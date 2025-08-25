import { test, expect } from 'vitest';
import fc from 'fast-check';
import { aeAssertRepro } from '../../src/testing/fc-assert.js';
import { expectMultisetEqual } from '../../src/testing/properties.js';

test('sort preserves multiset (with repro)', () => {
  aeAssertRepro('sort_multiset', fc.property(fc.array(fc.integer()), (arr) => {
    const sorted = [...arr].sort((a, b) => a - b);
    
    // This should pass - just checking multiset equality
    expectMultisetEqual(sorted, arr);
    
    // This assertion will intentionally fail for arrays with length > 3
    // to demonstrate repro generation
    expect(sorted.length).toBeLessThanOrEqual(3);
  }));
});

test('string reverse property (with repro)', () => {
  aeAssertRepro('string_reverse', fc.property(fc.string(), (str) => {
    const reversed = str.split('').reverse().join('');
    const doubleReversed = reversed.split('').reverse().join('');
    
    // This should always pass
    expect(doubleReversed).toBe(str);
    
    // This will fail for strings longer than 2 characters
    // to demonstrate repro generation with different data types
    expect(str.length).toBeLessThanOrEqual(2);
  }));
});