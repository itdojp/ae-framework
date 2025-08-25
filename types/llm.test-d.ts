import { expectType } from 'tsd';
import type { LLM } from '../src/providers/index.js';

declare const llm: LLM;

// Test LLM interface compliance
expectType<Promise<string>>(llm.complete({ prompt: 'x' }));
expectType<Promise<string>>(llm.complete({ prompt: 'x', system: 'y' }));
expectType<Promise<string>>(llm.complete({ prompt: 'x', temperature: 0.5 }));
expectType<Promise<string>>(llm.complete({ prompt: 'x', system: 'y', temperature: 0.5 }));

// Test name property
expectType<string>(llm.name);