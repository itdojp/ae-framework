/**
 * @fileoverview Unified Service Manager Implementation
 * Phase 3: Services & Integration - Core service management
 * Unified manager for all service types with optimization and validation
 */
import { ServiceConfig, ServiceTask, ServiceResult, ServiceLifecycleResult, PerformanceMetrics, CoverageMetrics, ServiceLayerValidation, OptimizationConfig } from './service-types.js';
import { ServiceRegistry } from './service-registry.js';
/**
 * Unified service manager implementing service layer optimization
 */
export declare class UnifiedServiceManager {
    private registry;
    private initialized;
    private optimizationConfig;
    private performanceBaseline?;
    private taskExecutionCount;
    private totalExecutionTime;
    constructor(registry?: ServiceRegistry);
    /**
     * Initialize the service manager
     */
    initialize(): Promise<void>;
    /**
     * Shutdown the service manager
     */
    shutdown(): Promise<void>;
    /**
     * Register a service
     */
    registerService(config: ServiceConfig): Promise<boolean>;
    /**
     * Get a service by ID
     */
    getService(id: string): Promise<ServiceConfig | undefined>;
    /**
     * Start a service and its dependencies
     */
    startService(serviceId: string): Promise<ServiceLifecycleResult>;
    /**
     * Stop a service
     */
    stopService(serviceId: string): Promise<ServiceLifecycleResult>;
    /**
     * Execute a service task
     */
    executeTask(task: ServiceTask): Promise<ServiceResult>;
    /**
     * Enable performance optimizations
     */
    enableOptimizations(config: OptimizationConfig): Promise<void>;
    /**
     * Get performance baseline
     */
    getPerformanceBaseline(): Promise<PerformanceMetrics>;
    /**
     * Get current performance metrics
     */
    getCurrentPerformance(): Promise<PerformanceMetrics>;
    /**
     * Get coverage metrics
     */
    getCoverageMetrics(): Promise<CoverageMetrics>;
    /**
     * Validate service layer
     */
    validateServiceLayer(): Promise<ServiceLayerValidation>;
    /**
     * Check if service is registered
     */
    isServiceRegistered(id: string): boolean;
    /**
     * Unregister service
     */
    unregisterService(id: string): Promise<boolean>;
    /**
     * Get registry instance
     */
    getRegistry(): ServiceRegistry;
    /**
     * Route task to appropriate service handler
     */
    private routeTaskToService;
    /**
     * Handle approval service tasks
     */
    private handleApprovalTask;
    /**
     * Handle container service tasks
     */
    private handleContainerTask;
    /**
     * Handle MCP service tasks
     */
    private handleMcpTask;
    /**
     * Handle optimization tasks
     */
    private handleOptimizationTask;
    /**
     * Handle generic tasks
     */
    private handleGenericTask;
    /**
     * Perform service-specific startup
     */
    private performServiceStartup;
    /**
     * Perform service-specific shutdown
     */
    private performServiceShutdown;
    /**
     * Measure current performance
     */
    private measureCurrentPerformance;
    /**
     * Calculate current throughput
     */
    private calculateThroughput;
    /**
     * Check if performance has improved
     */
    private hasPerformanceImprovement;
}
