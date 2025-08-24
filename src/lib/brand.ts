import { z } from 'zod';

export type Brand<T, B extends string> = T & { readonly __brand: B };

export function branded<T, B extends string>(
  schema: z.ZodType<T>, brand: B, normalize?: (t: T) => T
) {
  return {
    schema,
    make(input: unknown): Brand<T, B> {
      if (normalize && typeof input === 'string') {
        input = normalize(input as T);
      }
      const v = schema.parse(input);
      return v as Brand<T, B>;
    },
    is(u: unknown): u is Brand<T, B> {
      try { 
        schema.parse(u); 
        return true; 
      } catch { 
        return false; 
      }
    }
  };
}