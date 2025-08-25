import { type Result } from '../../core/result.js';
import type { AppError } from '../../core/errors.js';
export declare function verifyRun(): Promise<Result<{
    logs: string[];
    duration: string;
}, AppError>>;
