/**
 * @fileoverview Unified Service Layer Tests
 * Phase 3: Services & Integration - Service layer reconstruction
 * Goal: Test-driven reconstruction of service layer with optimization
 */

import { describe, test, expect, beforeEach, afterEach } from 'vitest';
import { UnifiedServiceManager } from '../../src/services/unified-service-manager.js';
import { ServiceRegistry } from '../../src/services/service-registry.js';
import { ServiceTask, ServiceType, ServiceResult, ServiceConfig } from '../../src/services/service-types.js';

describe('UnifiedServiceManager - Service Layer Architecture', () => {
  let serviceManager: UnifiedServiceManager;
  let serviceRegistry: ServiceRegistry;

  beforeEach(async () => {
    serviceRegistry = new ServiceRegistry();
    serviceManager = new UnifiedServiceManager(serviceRegistry);
    await serviceManager.initialize();
  });

  afterEach(async () => {
    await serviceManager.shutdown();
  });

  describe('Core Service Management', () => {
    test('should register and manage all service types', async () => {
      const serviceConfig: ServiceConfig = {
        id: 'test-approval-service',
        type: ServiceType.APPROVAL,
        config: {
          autoApprove: false,
          requiresHuman: true,
          timeout: 30000
        },
        dependencies: []
      };

      const registered = await serviceManager.registerService(serviceConfig);
      expect(registered).toBe(true);

      const service = await serviceManager.getService('test-approval-service');
      expect(service).toBeDefined();
      expect(service?.type).toBe(ServiceType.APPROVAL);
    });

    test('should handle service dependencies correctly', async () => {
      const baseService: ServiceConfig = {
        id: 'base-service',
        type: ServiceType.CONTAINER,
        config: { engine: 'docker' },
        dependencies: []
      };

      const dependentService: ServiceConfig = {
        id: 'dependent-service',
        type: ServiceType.MCP,
        config: { serverUrl: 'localhost:3000' },
        dependencies: ['base-service']
      };

      await serviceManager.registerService(baseService);
      await serviceManager.registerService(dependentService);

      const startResult = await serviceManager.startService('dependent-service');
      expect(startResult.success).toBe(true);
      expect(startResult.dependenciesAffected).toBeDefined();
      expect(startResult.dependenciesAffected?.length).toBeGreaterThan(0);
    });

    test('should optimize service performance', async () => {
      const task: ServiceTask = {
        id: 'performance-test',
        type: ServiceType.OPTIMIZATION,
        specification: {
          requirements: 'Optimize service layer performance',
          acceptance: ['Response time < 100ms', 'Memory usage optimized'],
          context: { enableCaching: true, enablePooling: true }
        },
        metadata: {
          priority: 1,
          estimatedDuration: 5000
        }
      };

      const result = await serviceManager.executeTask(task);

      expect(result.success).toBe(true);
      expect(result.performanceMetrics).toBeDefined();
      expect(result.performanceMetrics?.responseTime).toBeLessThan(100);
      expect(result.performanceMetrics?.memoryOptimized).toBe(true);
    });
  });

  describe('Service Integration', () => {
    test('should integrate with approval service workflows', async () => {
      const approvalConfig: ServiceConfig = {
        id: 'approval-service',
        type: ServiceType.APPROVAL,
        config: {
          autoApprove: false,
          requiresHuman: false, // For testing
          timeout: 5000
        },
        dependencies: []
      };

      await serviceManager.registerService(approvalConfig);

      const approvalTask: ServiceTask = {
        id: 'approval-test',
        type: ServiceType.APPROVAL,
        specification: {
          requirements: 'Test approval workflow integration',
          acceptance: ['Approval processed', 'Result recorded'],
          context: { 
            approvalType: 'phase-transition',
            data: { fromPhase: '2-agents', toPhase: '3-services' }
          }
        },
        metadata: { priority: 1, estimatedDuration: 2000 }
      };

      const result = await serviceManager.executeTask(approvalTask);

      expect(result.success).toBe(true);
      expect(result.approvalResult).toBeDefined();
      expect(result.approvalResult?.approved).toBe(true);
    });

    test('should integrate with container services', async () => {
      const containerConfig: ServiceConfig = {
        id: 'container-service',
        type: ServiceType.CONTAINER,
        config: {
          engine: 'docker',
          registries: ['docker.io'],
          networkMode: 'bridge'
        },
        dependencies: []
      };

      await serviceManager.registerService(containerConfig);

      const containerTask: ServiceTask = {
        id: 'container-test',
        type: ServiceType.CONTAINER,
        specification: {
          requirements: 'Test container service integration',
          acceptance: ['Container started', 'Health check passed'],
          context: {
            image: 'node:18-alpine',
            command: ['echo', 'hello world']
          }
        },
        metadata: { priority: 1, estimatedDuration: 10000 }
      };

      const result = await serviceManager.executeTask(containerTask);

      expect(result.success).toBe(true);
      expect(result.containerResult).toBeDefined();
      expect(result.containerResult?.containerId).toBeDefined();
    });

    test('should integrate with MCP server services', async () => {
      const mcpConfig: ServiceConfig = {
        id: 'mcp-service',
        type: ServiceType.MCP,
        config: {
          serverUrl: 'http://localhost:3001',
          protocol: 'stdio',
          capabilities: ['tools', 'resources']
        },
        dependencies: []
      };

      await serviceManager.registerService(mcpConfig);

      const mcpTask: ServiceTask = {
        id: 'mcp-test',
        type: ServiceType.MCP,
        specification: {
          requirements: 'Test MCP server integration',
          acceptance: ['Connection established', 'Tools available'],
          context: {
            action: 'list_tools',
            parameters: {}
          }
        },
        metadata: { priority: 1, estimatedDuration: 3000 }
      };

      const result = await serviceManager.executeTask(mcpTask);

      expect(result.success).toBe(true);
      expect(result.mcpResult).toBeDefined();
      expect(result.mcpResult?.toolsAvailable).toBeGreaterThan(0);
    });
  });

  describe('Performance Optimization', () => {
    test('should meet 80% test coverage threshold', async () => {
      const coverageResult = await serviceManager.getCoverageMetrics();

      expect(coverageResult.lineCoverage).toBeGreaterThanOrEqual(0.8);
      expect(coverageResult.branchCoverage).toBeGreaterThanOrEqual(0.8);
      expect(coverageResult.functionCoverage).toBeGreaterThanOrEqual(0.8);
    });

    test('should demonstrate performance improvements', async () => {
      const baseline = await serviceManager.getPerformanceBaseline();
      
      // Enable optimizations
      await serviceManager.enableOptimizations({
        caching: true,
        connectionPooling: true,
        requestBatching: true
      });

      const optimized = await serviceManager.getCurrentPerformance();

      expect(optimized.averageResponseTime).toBeLessThan(baseline.averageResponseTime);
      expect(optimized.memoryUsage).toBeLessThanOrEqual(baseline.memoryUsage);
      expect(optimized.throughput).toBeGreaterThan(baseline.throughput);
    });

    test('should validate service layer optimization', async () => {
      // Enable optimizations first
      await serviceManager.enableOptimizations({
        caching: true,
        connectionPooling: true,
        requestBatching: true
      });

      const validationResult = await serviceManager.validateServiceLayer();

      expect(validationResult.serviceLayerOptimized).toBe(true);
      expect(validationResult.performanceImproved).toBe(true);
      expect(validationResult.typeScriptCompliant).toBe(true);
      expect(validationResult.errorCount).toBe(0);
    });
  });

  describe('Service Registry', () => {
    test('should maintain service registry integrity', async () => {
      const registry = serviceManager.getRegistry();
      
      // Register test services first
      await serviceManager.registerService({
        id: 'test-approval',
        type: ServiceType.APPROVAL,
        config: {},
        dependencies: []
      });
      
      expect(registry.getServiceCount()).toBeGreaterThanOrEqual(1);
      expect(registry.getAllServices()).toBeDefined();
      expect(registry.getServiceTypes()).toContain(ServiceType.APPROVAL);
    });

    test('should handle service lifecycle management', async () => {
      const serviceConfig: ServiceConfig = {
        id: 'lifecycle-test-service',
        type: ServiceType.APPROVAL,
        config: { autoApprove: true, timeout: 1000 },
        dependencies: []
      };

      // Register
      await serviceManager.registerService(serviceConfig);
      expect(serviceManager.isServiceRegistered('lifecycle-test-service')).toBe(true);

      // Start
      const startResult = await serviceManager.startService('lifecycle-test-service');
      expect(startResult.success).toBe(true);

      // Stop
      const stopResult = await serviceManager.stopService('lifecycle-test-service');
      expect(stopResult.success).toBe(true);

      // Unregister
      const unregisterResult = await serviceManager.unregisterService('lifecycle-test-service');
      expect(unregisterResult).toBe(true);
      expect(serviceManager.isServiceRegistered('lifecycle-test-service')).toBe(false);
    });
  });
});