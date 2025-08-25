/**
 * Type tests for assertNever utility
 */
import { expectType, expectError } from 'tsd';
import { assertNever } from '../src/core/assertNever.js';

// Test: assertNever accepts never type
declare const neverValue: never;
expectType<never>(assertNever(neverValue));

// Test: assertNever rejects string
expectError(assertNever('string'));

// Test: assertNever rejects number
expectError(assertNever(42));

// Test: assertNever rejects boolean
expectError(assertNever(true));

// Test: assertNever rejects object
expectError(assertNever({}));

// Test: assertNever rejects undefined
expectError(assertNever(undefined));

// Test: assertNever rejects null
expectError(assertNever(null));

// Test: exhaustive switch pattern
enum TestEnum {
  A = 'a',
  B = 'b',
  C = 'c'
}

// eslint-disable-next-line @typescript-eslint/no-unused-vars
function exhaustiveSwitch(value: TestEnum): string {
  switch (value) {
    case TestEnum.A:
      return 'A';
    case TestEnum.B:
      return 'B';
    case TestEnum.C:
      return 'C';
    default:
      // This should compile because all cases are handled
      return assertNever(value);
  }
}

// Test: non-exhaustive switch should error
// eslint-disable-next-line @typescript-eslint/no-unused-vars
function nonExhaustiveSwitch(value: TestEnum): string {
  switch (value) {
    case TestEnum.A:
      return 'A';
    case TestEnum.B:
      return 'B';
    // Missing case TestEnum.C
    default:
      // This should error because TestEnum.C is not handled
      expectError(assertNever(value));
      return 'unreachable';
  }
}