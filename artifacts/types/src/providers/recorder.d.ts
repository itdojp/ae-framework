import type { LLM } from './index.js';
export declare function withRecorder(base: LLM, opts?: {
    dir?: string;
    replay?: boolean;
}): LLM;
