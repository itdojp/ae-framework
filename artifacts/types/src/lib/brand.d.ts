import { z } from 'zod';
export type Brand<T, B extends string> = T & {
    readonly __brand: B;
};
export declare function branded<T, B extends string>(schema: z.ZodType<T>, brand: B, normalize?: (t: T) => T): {
    schema: z.ZodType<T, z.ZodTypeDef, T>;
    make(input: unknown): Brand<T, B>;
    is(u: unknown): u is Brand<T, B>;
};
