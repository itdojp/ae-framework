/**
 * Phase status for tracking completion and approval
 */
export interface PhaseStatus {
    completed: boolean;
    approved: boolean;
    startedAt?: Date;
    completedAt?: Date;
    approvedAt?: Date;
    approvedBy?: string;
    artifacts: string[];
    notes?: string;
}
/**
 * Project phase state
 */
export interface PhaseState {
    projectId: string;
    projectName?: string;
    createdAt: Date;
    updatedAt: Date;
    currentPhase: PhaseType;
    phaseStatus: {
        intent: PhaseStatus;
        formal: PhaseStatus;
        test: PhaseStatus;
        code: PhaseStatus;
        verify: PhaseStatus;
        operate: PhaseStatus;
    };
    approvalsRequired: boolean;
    metadata?: Record<string, any>;
}
/**
 * Phase types in ae-framework
 */
export type PhaseType = 'intent' | 'formal' | 'test' | 'code' | 'verify' | 'operate';
/**
 * PhaseStateManager manages the state of project phases
 */
export declare class PhaseStateManager {
    private stateFilePath;
    private state;
    constructor(projectRoot?: string);
    /**
     * Initialize a new project state
     */
    initializeProject(projectName?: string, approvalsRequired?: boolean): Promise<PhaseState>;
    /**
     * Load existing project state
     */
    loadState(): Promise<PhaseState | null>;
    /**
     * Save state to file
     */
    private saveState;
    /**
     * Get current state
     */
    getCurrentState(): Promise<PhaseState | null>;
    /**
     * Start a phase
     */
    startPhase(phase: PhaseType): Promise<void>;
    /**
     * Complete a phase
     */
    completePhase(phase: PhaseType, artifacts: string[]): Promise<void>;
    /**
     * Approve a phase
     */
    approvePhase(phase: PhaseType, approvedBy: string, notes?: string): Promise<void>;
    /**
     * Check if can transition to next phase
     */
    canTransitionToNextPhase(): Promise<boolean>;
    /**
     * Transition to next phase
     */
    transitionToNextPhase(): Promise<PhaseType | null>;
    /**
     * Get next phase
     */
    getNextPhase(currentPhase: PhaseType): PhaseType | null;
    /**
     * Get phase progress percentage
     */
    getProgressPercentage(): Promise<number>;
    /**
     * Get phase timeline
     */
    getPhaseTimeline(): Promise<Array<{
        phase: PhaseType;
        startedAt?: Date;
        completedAt?: Date;
        duration?: number;
        status: 'pending' | 'in-progress' | 'completed' | 'approved';
    }>>;
    /**
     * Add metadata to state
     */
    addMetadata(key: string, value: any): Promise<void>;
    /**
     * Get artifacts for a phase
     */
    getPhaseArtifacts(phase: PhaseType): Promise<string[]>;
    /**
     * Generate status report
     */
    generateStatusReport(): Promise<string>;
    /**
     * Reset phase (for testing or rollback)
     */
    resetPhase(phase: PhaseType): Promise<void>;
    /**
     * Create empty phase status
     */
    private createEmptyPhaseStatus;
    /**
     * Check if project exists
     */
    hasProject(): Promise<boolean>;
}
