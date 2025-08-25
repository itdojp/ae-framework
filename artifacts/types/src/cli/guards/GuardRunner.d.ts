import { AEFrameworkConfig, Guard, GuardResult } from '../types.js';
export declare class GuardRunner {
    private config;
    constructor(config: AEFrameworkConfig);
    run(guard: Guard): Promise<GuardResult>;
    private runTDDGuard;
    private runTestExecutionGuard;
    private runRedGreenCycleGuard;
    private runCoverageGuard;
    checkGitForTDDViolations(): Promise<string[]>;
}
