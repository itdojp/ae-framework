import { z } from 'zod';
import { branded, Brand } from './brand.js';

const EmailSchema = z.string().email();
export type Email = Brand<string, 'Email'>;

export const Email = branded(
  EmailSchema, 
  'Email', 
  (s) => s.trim().toLowerCase()
);

export function makeEmail(input: string): Email { 
  return Email.make(input); 
}