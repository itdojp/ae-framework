import { type Result } from './result.js';
import type { AppError } from './errors.js';
export declare function run(step: string, cmd: string, args: string[], opts?: any): Promise<Result<{
    stdout: string;
}, AppError>>;
