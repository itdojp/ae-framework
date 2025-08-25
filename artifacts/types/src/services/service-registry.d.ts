/**
 * @fileoverview Service Registry Implementation
 * Phase 3: Services & Integration - Service registry for unified management
 * Manages registration and lifecycle of all services
 */
import { ServiceConfig, ServiceType, ServiceState, ServiceRegistryInterface } from './service-types.js';
/**
 * Centralized service registry for the unified service layer
 */
export declare class ServiceRegistry implements ServiceRegistryInterface {
    private services;
    private serviceStates;
    private dependencyGraph;
    constructor();
    /**
     * Register a new service in the registry
     */
    registerService(config: ServiceConfig): Promise<boolean>;
    /**
     * Unregister a service from the registry
     */
    unregisterService(id: string): Promise<boolean>;
    /**
     * Get service configuration by ID
     */
    getService(id: string): Promise<ServiceConfig | undefined>;
    /**
     * Get all registered services
     */
    getAllServices(): Promise<ServiceConfig[]>;
    /**
     * Get services by type
     */
    getServicesByType(type: ServiceType): Promise<ServiceConfig[]>;
    /**
     * Get total number of registered services
     */
    getServiceCount(): number;
    /**
     * Get all unique service types
     */
    getServiceTypes(): ServiceType[];
    /**
     * Get service state
     */
    getServiceState(id: string): ServiceState | undefined;
    /**
     * Update service state
     */
    updateServiceState(id: string, updates: Partial<ServiceState>): boolean;
    /**
     * Get services that depend on the given service
     */
    getDependents(serviceId: string): string[];
    /**
     * Get dependencies of a service
     */
    getDependencies(serviceId: string): string[];
    /**
     * Check if service is registered
     */
    isServiceRegistered(id: string): boolean;
    /**
     * Get services in dependency order (topological sort)
     */
    getServicesInDependencyOrder(): string[];
    /**
     * Validate service registry integrity
     */
    validateRegistry(): Array<{
        issue: string;
        severity: 'error' | 'warning';
    }>;
    /**
     * Clear all services (for testing)
     */
    clear(): void;
    /**
     * Update dependency graph for a service
     */
    private updateDependencyGraph;
}
