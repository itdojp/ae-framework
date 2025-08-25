/**
 * @fileoverview Service Layer Domain Types
 * Phase 3: Services & Integration - Service layer type definitions
 * Core domain types for unified service layer architecture
 */
/**
 * Service types supported by the unified service layer
 */
export declare enum ServiceType {
    APPROVAL = "approval",
    CONTAINER = "container",
    MCP = "mcp",
    PERSONA = "persona",
    OPTIMIZATION = "optimization",
    INTEGRATION = "integration",
    MONITORING = "monitoring"
}
/**
 * Service configuration structure
 */
export interface ServiceConfig {
    id: string;
    type: ServiceType;
    config: Record<string, any>;
    dependencies: string[];
    enabled?: boolean;
    timeout?: number;
}
/**
 * Service task specification
 */
export interface ServiceTaskSpecification {
    requirements: string;
    acceptance: string[];
    context: Record<string, any>;
}
/**
 * Service task definition
 */
export interface ServiceTask {
    id: string;
    type: ServiceType;
    specification: ServiceTaskSpecification;
    metadata: {
        priority: number;
        estimatedDuration: number;
        dependencies?: string[];
        deadline?: Date;
    };
}
/**
 * Service execution result
 */
export interface ServiceResult {
    success: boolean;
    taskId: string;
    serviceId?: string;
    artifacts: string[];
    performanceMetrics?: {
        responseTime: number;
        memoryOptimized: boolean;
        throughput: number;
        cacheHitRate?: number;
    };
    approvalResult?: {
        approved: boolean;
        approver?: string;
        timestamp: Date;
        reason?: string;
    };
    containerResult?: {
        containerId: string;
        status: string;
        exitCode?: number;
        logs?: string[];
    };
    mcpResult?: {
        toolsAvailable: number;
        resourcesAvailable: number;
        connectionStatus: string;
        capabilities: string[];
    };
    dependenciesAffected?: string[];
    errors?: string[];
}
/**
 * Service state management
 */
export interface ServiceState {
    id: string;
    status: 'registered' | 'starting' | 'running' | 'stopping' | 'stopped' | 'error';
    startedAt?: Date;
    stoppedAt?: Date;
    errorMessage?: string;
    healthStatus: 'healthy' | 'unhealthy' | 'unknown';
}
/**
 * Service registry interface
 */
export interface ServiceRegistryInterface {
    registerService(config: ServiceConfig): Promise<boolean>;
    unregisterService(id: string): Promise<boolean>;
    getService(id: string): Promise<ServiceConfig | undefined>;
    getAllServices(): Promise<ServiceConfig[]>;
    getServicesByType(type: ServiceType): Promise<ServiceConfig[]>;
    getServiceCount(): number;
    getServiceTypes(): ServiceType[];
}
/**
 * Performance metrics tracking
 */
export interface PerformanceMetrics {
    averageResponseTime: number;
    memoryUsage: number;
    throughput: number;
    errorRate: number;
    uptime: number;
}
/**
 * Coverage metrics for validation
 */
export interface CoverageMetrics {
    lineCoverage: number;
    branchCoverage: number;
    functionCoverage: number;
    statementCoverage: number;
}
/**
 * Service layer validation result
 */
export interface ServiceLayerValidation {
    serviceLayerOptimized: boolean;
    performanceImproved: boolean;
    typeScriptCompliant: boolean;
    errorCount: number;
    coverageThresholdMet: boolean;
    validationDetails: Array<{
        check: string;
        passed: boolean;
        message: string;
        value?: any;
    }>;
}
/**
 * Optimization configuration
 */
export interface OptimizationConfig {
    caching: boolean;
    connectionPooling: boolean;
    requestBatching: boolean;
    compressionEnabled?: boolean;
    timeoutOptimization?: boolean;
}
/**
 * Service lifecycle management
 */
export interface ServiceLifecycleResult {
    success: boolean;
    serviceId: string;
    action: 'start' | 'stop' | 'restart' | 'health-check';
    timestamp: Date;
    duration: number;
    dependenciesAffected?: string[];
    message?: string;
}
