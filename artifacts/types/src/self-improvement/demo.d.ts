/**
 * ae-framework Self-Improvement TDD Infrastructure Demo
 *
 * This module demonstrates the complete TDD infrastructure setup and validates
 * all components are working correctly for the self-improvement project.
 */
export interface DemoConfig {
    projectRoot: string;
    configFile: string;
    validateComponents: boolean;
    runSampleTDDCycle: boolean;
}
export declare class SelfImprovementDemo {
    private config;
    private tddSetup?;
    private gitHooksSetup?;
    constructor(config?: Partial<DemoConfig>);
    /**
     * Run complete TDD infrastructure demonstration
     */
    runDemo(): Promise<{
        success: boolean;
        phases: Array<{
            phase: string;
            success: boolean;
            message: string;
            duration: number;
        }>;
        summary: string;
    }>;
    /**
     * Run a single phase with timing and error handling
     */
    private runPhase;
    /**
     * Validate ae-framework-v2.yml configuration
     */
    private validateConfiguration;
    /**
     * Set up TDD infrastructure
     */
    private setupTDDInfrastructure;
    /**
     * Set up git hooks
     */
    private setupGitHooks;
    /**
     * Validate all components are working
     */
    private validateAllComponents;
    /**
     * Run a sample TDD cycle to demonstrate functionality
     */
    private runSampleTDDCycle;
    /**
     * Generate final report
     */
    private generateFinalReport;
    /**
     * Generate summary of demo results
     */
    private generateSummary;
}
export declare const createSelfImprovementDemo: (config?: Partial<DemoConfig>) => SelfImprovementDemo;
export declare const runSelfImprovementDemo: () => Promise<never>;
