import { z } from 'zod';
import { Brand } from './brand.js';
export type Email = Brand<string, 'Email'>;
export declare const Email: {
    schema: z.ZodType<string, z.ZodTypeDef, string>;
    make(input: unknown): Brand<string, "Email">;
    is(u: unknown): u is Brand<string, "Email">;
};
export declare function makeEmail(input: string): Email;
