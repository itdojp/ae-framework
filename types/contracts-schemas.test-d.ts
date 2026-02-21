import { expectNotType, expectType } from 'tsd';
import type { z } from 'zod';
import { InputSchema, OutputSchema } from '../src/contracts/schemas.js';

type InputType = z.infer<typeof InputSchema>;
type OutputType = z.infer<typeof OutputSchema>;

declare const inputValue: InputType;
declare const outputValue: OutputType;

expectType<unknown>(inputValue);
expectType<unknown>(outputValue);
expectNotType<any>(inputValue);
expectNotType<any>(outputValue);
