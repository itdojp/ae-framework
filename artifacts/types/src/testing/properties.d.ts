import fc from 'fast-check';
export declare const arbEmail: fc.Arbitrary<string>;
export declare function multiset<T>(arr: T[]): Map<T, number>;
export declare function expectMultisetEqual<T>(a: T[], b: T[]): void;
