import { expectType } from 'tsd';
import type { z } from 'zod';
import { InputSchema, OutputSchema } from '../src/contracts/schemas.js';

type InputType = z.infer<typeof InputSchema>;
type OutputType = z.infer<typeof OutputSchema>;
type IsAny<T> = 0 extends (1 & T) ? true : false;

declare const inputValue: InputType;
declare const outputValue: OutputType;

expectType<unknown>(inputValue);
expectType<unknown>(outputValue);
expectType<false>(false as IsAny<InputType>);
expectType<false>(false as IsAny<OutputType>);
