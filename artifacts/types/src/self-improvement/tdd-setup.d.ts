/**
 * TDD Infrastructure Setup for ae-framework Self-Improvement
 *
 * This module configures and initializes the TDD infrastructure using
 * ae-framework's existing components for quality-controlled reimplementation.
 */
import { HybridTDDSystem } from '../integration/hybrid-tdd-system.js';
import { TDDAgent } from '../agents/tdd-agent.js';
import { MetricsCollector } from '../cli/metrics/MetricsCollector.js';
export interface SelfImprovementTDDConfig {
    projectRoot: string;
    configFile: string;
    enableRealTimeMonitoring: boolean;
    strictModeEnforcement: boolean;
    targetCoverage: number;
    metricsOutputPath: string;
}
export declare class SelfImprovementTDDSetup {
    private hybridTDD?;
    private tddAgent?;
    private metricsCollector?;
    private config;
    constructor(config?: Partial<SelfImprovementTDDConfig>);
    /**
     * Initialize TDD infrastructure for self-improvement project
     */
    initializeTDDInfrastructure(): Promise<{
        success: boolean;
        components: {
            hybridTDD: boolean;
            tddAgent: boolean;
            metricsCollector: boolean;
        };
        message: string;
    }>;
    /**
     * Load self-improvement configuration
     */
    private loadSelfImprovementConfig;
    /**
     * Set up HybridTDDSystem for Claude Code integration
     */
    private setupHybridTDDSystem;
    /**
     * Configure TDDAgent for real-time enforcement
     */
    private setupTDDAgent;
    /**
     * Initialize MetricsCollector for progress tracking
     */
    private setupMetricsCollector;
    /**
     * Validate TDD infrastructure is operational
     */
    validateTDDInfrastructure(): Promise<{
        operational: boolean;
        checks: {
            hybridTDDActive: boolean;
            tddAgentReady: boolean;
            metricsCollecting: boolean;
            configValid: boolean;
        };
        recommendations: string[];
    }>;
    /**
     * Get TDD system instance for external use
     */
    getHybridTDDSystem(): HybridTDDSystem | undefined;
    /**
     * Get TDD Agent instance for external use
     */
    getTDDAgent(): TDDAgent | undefined;
    /**
     * Get MetricsCollector instance for external use
     */
    getMetricsCollector(): MetricsCollector | undefined;
    /**
     * Generate initial setup report
     */
    generateSetupReport(): string;
}
export declare const createSelfImprovementTDDSetup: (config?: Partial<SelfImprovementTDDConfig>) => SelfImprovementTDDSetup;
