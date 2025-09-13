/**
 * @fileoverview Service Registry Implementation
 * Phase 3: Services & Integration - Service registry for unified management
 * Manages registration and lifecycle of all services
 */

import type { 
  ServiceConfig, 
  ServiceType, 
  ServiceState,
  ServiceRegistryInterface 
} from './service-types.js';

/**
 * Centralized service registry for the unified service layer
 */
export class ServiceRegistry implements ServiceRegistryInterface {
  private services: Map<string, ServiceConfig> = new Map();
  private serviceStates: Map<string, ServiceState> = new Map();
  private dependencyGraph: Map<string, Set<string>> = new Map();

  constructor() {
    // Initialize empty registry
  }

  /**
   * Register a new service in the registry
   */
  async registerService(config: ServiceConfig): Promise<boolean> {
    try {
      // Validate service configuration
      if (!config.id || !config.type) {
        throw new Error('Service ID and type are required');
      }

      // Check if service already exists
      if (this.services.has(config.id)) {
        throw new Error(`Service with ID ${config.id} already registered`);
      }

      // Validate dependencies exist
      for (const depId of config.dependencies) {
        if (!this.services.has(depId)) {
          throw new Error(`Dependency service ${depId} not found`);
        }
      }

      // Store service configuration
      this.services.set(config.id, { ...config, enabled: config.enabled ?? true });

      // Initialize service state
      const initialState: ServiceState = {
        id: config.id,
        status: 'registered',
        healthStatus: 'unknown'
      };
      this.serviceStates.set(config.id, initialState);

      // Update dependency graph
      this.updateDependencyGraph(config);

      return true;
    } catch (error) {
      console.error(`Failed to register service ${config.id}:`, error);
      return false;
    }
  }

  /**
   * Unregister a service from the registry
   */
  async unregisterService(id: string): Promise<boolean> {
    try {
      if (!this.services.has(id)) {
        return false;
      }

      // Check if other services depend on this one
      const dependents = this.getDependents(id);
      if (dependents.length > 0) {
        throw new Error(`Cannot unregister service ${id}: dependencies exist (${dependents.join(', ')})`);
      }

      // Remove service and state
      this.services.delete(id);
      this.serviceStates.delete(id);

      // Clean up dependency graph
      this.dependencyGraph.delete(id);
      for (const [serviceId, deps] of this.dependencyGraph.entries()) {
        deps.delete(id);
      }

      return true;
    } catch (error) {
      console.error(`Failed to unregister service ${id}:`, error);
      return false;
    }
  }

  /**
   * Get service configuration by ID
   */
  async getService(id: string): Promise<ServiceConfig | undefined> {
    return this.services.get(id);
  }

  /**
   * Get all registered services
   */
  async getAllServices(): Promise<ServiceConfig[]> {
    return Array.from(this.services.values());
  }

  /**
   * Get services by type
   */
  async getServicesByType(type: ServiceType): Promise<ServiceConfig[]> {
    return Array.from(this.services.values()).filter(service => service.type === type);
  }

  /**
   * Get total number of registered services
   */
  getServiceCount(): number {
    return this.services.size;
  }

  /**
   * Get all unique service types
   */
  getServiceTypes(): ServiceType[] {
    const types = new Set<ServiceType>();
    for (const service of this.services.values()) {
      types.add(service.type);
    }
    return Array.from(types);
  }

  /**
   * Get service state
   */
  getServiceState(id: string): ServiceState | undefined {
    return this.serviceStates.get(id);
  }

  /**
   * Update service state
   */
  updateServiceState(id: string, updates: Partial<ServiceState>): boolean {
    const currentState = this.serviceStates.get(id);
    if (!currentState) {
      return false;
    }

    const newState: ServiceState = {
      ...currentState,
      ...updates
    };

    this.serviceStates.set(id, newState);
    return true;
  }

  /**
   * Get services that depend on the given service
   */
  getDependents(serviceId: string): string[] {
    const dependents: string[] = [];
    
    for (const [id, deps] of this.dependencyGraph.entries()) {
      if (deps.has(serviceId)) {
        dependents.push(id);
      }
    }

    return dependents;
  }

  /**
   * Get dependencies of a service
   */
  getDependencies(serviceId: string): string[] {
    const deps = this.dependencyGraph.get(serviceId);
    return deps ? Array.from(deps) : [];
  }

  /**
   * Check if service is registered
   */
  isServiceRegistered(id: string): boolean {
    return this.services.has(id);
  }

  /**
   * Get services in dependency order (topological sort)
   */
  getServicesInDependencyOrder(): string[] {
    const visited = new Set<string>();
    const temp = new Set<string>();
    const result: string[] = [];

    const visit = (serviceId: string): void => {
      if (temp.has(serviceId)) {
        throw new Error(`Circular dependency detected involving service ${serviceId}`);
      }
      if (visited.has(serviceId)) {
        return;
      }

      temp.add(serviceId);
      const deps = this.dependencyGraph.get(serviceId) || new Set();
      for (const dep of deps) {
        visit(dep);
      }
      temp.delete(serviceId);
      visited.add(serviceId);
      result.push(serviceId);
    };

    // Visit all services
    for (const serviceId of this.services.keys()) {
      if (!visited.has(serviceId)) {
        visit(serviceId);
      }
    }

    return result;
  }

  /**
   * Validate service registry integrity
   */
  validateRegistry(): Array<{ issue: string; severity: 'error' | 'warning' }> {
    const issues: Array<{ issue: string; severity: 'error' | 'warning' }> = [];

    // Check for missing dependencies
    for (const [serviceId, config] of this.services.entries()) {
      for (const depId of config.dependencies) {
        if (!this.services.has(depId)) {
          issues.push({
            issue: `Service ${serviceId} depends on non-existent service ${depId}`,
            severity: 'error'
          });
        }
      }
    }

    // Check for circular dependencies
    try {
      this.getServicesInDependencyOrder();
    } catch (error) {
      issues.push({
        issue: `Circular dependency detected: ${error instanceof Error ? error.message : 'Unknown error'}`,
        severity: 'error'
      });
    }

    // Check for orphaned states
    for (const stateId of this.serviceStates.keys()) {
      if (!this.services.has(stateId)) {
        issues.push({
          issue: `Orphaned service state found for ${stateId}`,
          severity: 'warning'
        });
      }
    }

    return issues;
  }

  /**
   * Clear all services (for testing)
   */
  clear(): void {
    this.services.clear();
    this.serviceStates.clear();
    this.dependencyGraph.clear();
  }

  /**
   * Update dependency graph for a service
   */
  private updateDependencyGraph(config: ServiceConfig): void {
    const dependencies = new Set(config.dependencies);
    this.dependencyGraph.set(config.id, dependencies);
  }
}
