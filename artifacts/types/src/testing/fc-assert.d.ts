import fc from 'fast-check';
export declare function aeAssert<T>(prop: fc.IProperty<T>, opts?: Partial<fc.Parameters<T>>): void;
export declare function aeAssertRepro<T>(name: string, prop: fc.IProperty<T>, opts?: Partial<fc.Parameters<T>>): void;
