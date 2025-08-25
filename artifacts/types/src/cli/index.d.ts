#!/usr/bin/env node
import { Phase } from './types.js';
import { TaskRequest, TaskResponse, TaskHandler } from '../agents/task-types.js';
import '../telemetry/telemetry-setup.js';
type TaskResult = TaskResponse;
declare class AEFrameworkCLI {
    private config;
    private phaseValidator;
    private guardRunner;
    private intentSystem;
    naturalLanguageHandler: TaskHandler;
    userStoriesHandler: TaskHandler;
    validationHandler: TaskHandler;
    domainModelingHandler: TaskHandler;
    uiHandler: TaskHandler;
    constructor();
    checkPhase(phaseName: string): Promise<void>;
    runGuards(guardName?: string): Promise<void>;
    runIntent(options: {
        analyze?: boolean;
        validate?: boolean;
        sources?: string;
    }): Promise<void>;
    handleProgressBlocking(result: TaskResult): void;
    nextPhase(): Promise<void>;
    detectCurrentPhase(): Promise<string>;
    getNextPhase(currentPhase: string): string | null;
    displayResults(details: Array<{
        check: string;
        passed: boolean;
        message?: string;
    }>): void;
    displayPhaseRequirements(phase: Phase): void;
    handleUIScaffoldTask(request: TaskRequest): Promise<TaskResponse>;
}
export { AEFrameworkCLI };
