import { type Result } from '../../core/result.js';
import type { AppError } from '../../core/errors.js';
interface QAFlakeOptions {
    times?: number;
    pattern?: string;
    timeoutMs?: number;
    workers?: string | number;
}
export declare function qaFlake(options?: QAFlakeOptions): Promise<Result<{
    failures: number;
    total: number;
    seeds: number[];
}, AppError>>;
export {};
