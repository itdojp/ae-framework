/**
 * @fileoverview System Validation Integration Tests
 * Phase 4: Validation & Quality Assurance - Comprehensive system validation
 * Goal: End-to-end validation of the unified architecture
 */

import { describe, test, expect, beforeEach } from 'vitest';
import { UnifiedAgent } from '../../src/agents/unified-agent.js';
import { UnifiedServiceManager } from '../../src/services/unified-service-manager.js';
import { ServiceRegistry } from '../../src/services/service-registry.js';
import { 
  AgentTask, 
  TaskType as AgentTaskType,
  AgentConfig 
} from '../../src/agents/domain-types.js';
import { 
  ServiceTask, 
  ServiceType, 
  ServiceConfig 
} from '../../src/services/service-types.js';
import {
  createIntegrationTempDir,
  registerIntegrationCleanup,
  applyIntegrationRetry,
} from '../_helpers/integration-test-utils.js';

applyIntegrationRetry(test);

describe('System Validation - Phase 4 Integration Tests', () => {
  let agent: UnifiedAgent;
  let serviceManager: UnifiedServiceManager;
  let serviceRegistry: ServiceRegistry;
  let phaseStateRoot: string;
  let originalPhaseStateRoot: string | undefined;
  let originalPhaseStateFile: string | undefined;

  beforeEach(async () => {
    originalPhaseStateRoot = process.env.AE_PHASE_STATE_ROOT;
    originalPhaseStateFile = process.env.AE_PHASE_STATE_FILE;

    phaseStateRoot = await createIntegrationTempDir('ae-phase-state-');
    process.env.AE_PHASE_STATE_ROOT = phaseStateRoot;
    delete process.env.AE_PHASE_STATE_FILE;

    serviceRegistry = new ServiceRegistry();
    serviceManager = new UnifiedServiceManager(serviceRegistry);
    await serviceManager.initialize();

    const agentConfig: AgentConfig = {
      id: 'integration-test-agent',
      type: 'code-generation',
      capabilities: ['typescript', 'testing', 'validation', 'integration'],
      context: {
        projectRoot: '/integration-test',
        phase: 'code',
        tddEnabled: true,
        strictMode: true,
        coverageThreshold: 0.85
      }
    };

    agent = new UnifiedAgent(agentConfig);
    await agent.initialize();

    const previousRoot = originalPhaseStateRoot;
    const previousFile = originalPhaseStateFile;
    const currentManager = serviceManager;

    registerIntegrationCleanup(async () => {
      try {
        await currentManager.shutdown();
      } catch (error) {
        console.warn('System validation cleanup failed:', error);
      }

      if (previousRoot !== undefined) {
        process.env.AE_PHASE_STATE_ROOT = previousRoot;
      } else {
        delete process.env.AE_PHASE_STATE_ROOT;
      }

      if (previousFile !== undefined) {
        process.env.AE_PHASE_STATE_FILE = previousFile;
      } else {
        delete process.env.AE_PHASE_STATE_FILE;
      }
    });
  });

  describe('Agent-Service Integration', () => {
    test('should demonstrate unified agent and service collaboration', async () => {
      // Register approval service
      const approvalServiceConfig: ServiceConfig = {
        id: 'integration-approval-service',
        type: ServiceType.APPROVAL,
        config: {
          autoApprove: false,
          requiresHuman: false,
          timeout: 5000
        },
        dependencies: []
      };

      const registered = await serviceManager.registerService(approvalServiceConfig);
      expect(registered).toBe(true);

      // Start the service
      const startResult = await serviceManager.startService('integration-approval-service');
      expect(startResult.success).toBe(true);

      // Agent creates a task that requires service approval
      const agentTask: AgentTask = {
        id: 'agent-service-integration-test',
        type: AgentTaskType.CODE_GENERATION,
        specification: {
          requirements: 'Generate code with service approval workflow',
          acceptance: ['Code generated', 'Approval obtained', 'Integration verified'],
          context: {
            requiresApproval: true,
            serviceId: 'integration-approval-service'
          }
        },
        metadata: {
          priority: 1,
          estimatedComplexity: 0.6
        }
      };

      const agentResult = await agent.processTask(agentTask);
      expect(agentResult.success).toBe(true);

      // Service processes the approval request
      const serviceTask: ServiceTask = {
        id: 'approval-for-agent-task',
        type: ServiceType.APPROVAL,
        specification: {
          requirements: 'Process approval for agent-generated code',
          acceptance: ['Approval decision made', 'Result communicated'],
          context: {
            agentTaskId: agentTask.id,
            approvalType: 'code-generation'
          }
        },
        metadata: {
          priority: 1,
          estimatedDuration: 2000
        }
      };

      const serviceResult = await serviceManager.executeTask(serviceTask);
      expect(serviceResult.success).toBe(true);
      expect(serviceResult.approvalResult?.approved).toBe(true);

      // Verify integration success
      expect(agentResult.validation.typeScriptCompliant).toBe(true);
      expect(serviceResult.performanceMetrics).toBeDefined();
    });

    test('should maintain system consistency across phases', async () => {
      // Verify Phase 2 agent system is functional
      const phase2Task: AgentTask = {
        id: 'phase2-consistency-check',
        type: AgentTaskType.VALIDATION,
        specification: {
          requirements: 'Validate Phase 2 agent system consistency',
          acceptance: ['Agent system unified', 'Domain modeling functional'],
          context: { phaseValidation: true }
        },
        metadata: { priority: 1, estimatedComplexity: 0.4 }
      };

      const phase2Result = await agent.processTask(phase2Task);
      expect(phase2Result.success).toBe(true);
      expect(phase2Result.validation.typeScriptCompliant).toBe(true);

      // Verify Phase 3 service system is functional
      const phase3Task: ServiceTask = {
        id: 'phase3-consistency-check',
        type: ServiceType.OPTIMIZATION,
        specification: {
          requirements: 'Validate Phase 3 service layer consistency',
          acceptance: ['Service layer optimized', 'Performance improved'],
          context: { phaseValidation: true }
        },
        metadata: { priority: 1, estimatedDuration: 3000 }
      };

      const phase3Result = await serviceManager.executeTask(phase3Task);
      expect(phase3Result.success).toBe(true);
      expect(phase3Result.performanceMetrics?.memoryOptimized).toBe(true);

      // Both systems should work together
      expect(phase2Result.validation.errorCount).toBe(0);
      expect(phase3Result.performanceMetrics?.responseTime).toBeLessThan(100);
    });
  });

  describe('Quality Assurance Validation', () => {
    test('should meet 85% coverage threshold requirement', async () => {
      const coverageMetrics = await serviceManager.getCoverageMetrics();

      expect(coverageMetrics.lineCoverage).toBeGreaterThanOrEqual(0.85);
      expect(coverageMetrics.branchCoverage).toBeGreaterThanOrEqual(0.85);
      expect(coverageMetrics.functionCoverage).toBeGreaterThanOrEqual(0.85);
      expect(coverageMetrics.statementCoverage).toBeGreaterThanOrEqual(0.85);
    });

    test('should demonstrate quality improvements over baseline', async () => {
      const baseline = await serviceManager.getPerformanceBaseline();
      
      // Enable all optimizations for quality improvement
      await serviceManager.enableOptimizations({
        caching: true,
        connectionPooling: true,
        requestBatching: true,
        compressionEnabled: true,
        timeoutOptimization: true
      });

      const improved = await serviceManager.getCurrentPerformance();

      // Quality improvements validation
      expect(improved.averageResponseTime).toBeLessThan(baseline.averageResponseTime);
      expect(improved.errorRate).toBeLessThanOrEqual(baseline.errorRate);
      expect(improved.throughput).toBeGreaterThan(baseline.throughput);
      expect(improved.uptime).toBeGreaterThanOrEqual(baseline.uptime);

      // Specific improvement thresholds
      const responseImprovement = (baseline.averageResponseTime - improved.averageResponseTime) / baseline.averageResponseTime;
      const throughputImprovement = (improved.throughput - baseline.throughput) / baseline.throughput;

      expect(responseImprovement).toBeGreaterThan(0.1); // At least 10% improvement
      expect(throughputImprovement).toBeGreaterThan(0.2); // At least 20% improvement
    });

    test('should validate TypeScript compliance across all components', async () => {
      // Validate agent TypeScript compliance
      const agentValidation: AgentTask = {
        id: 'typescript-compliance-agent',
        type: AgentTaskType.VALIDATION,
        specification: {
          requirements: 'Validate TypeScript strict mode compliance',
          acceptance: ['Zero type errors', 'Strict mode compatible'],
          context: { strictMode: true, typeScriptValidation: true }
        },
        metadata: { priority: 1, estimatedComplexity: 0.3 }
      };

      const agentResult = await agent.processTask(agentValidation);
      expect(agentResult.success).toBe(true);
      expect(agentResult.validation.typeScriptCompliant).toBe(true);
      expect(agentResult.validation.strictModeCompatible).toBe(true);

      // Validate service TypeScript compliance
      await serviceManager.enableOptimizations({
        caching: true,
        connectionPooling: true,
        requestBatching: true,
        compressionEnabled: true,
        timeoutOptimization: true
      });

      const serviceValidation = await serviceManager.validateServiceLayer();
      expect(serviceValidation.typeScriptCompliant).toBe(true);
      expect(serviceValidation.errorCount).toBe(0);

      // Integration validation
      expect(agentResult.validation.errorCount).toBe(0);
      expect(serviceValidation.serviceLayerOptimized).toBe(true);
    });

    test('should pass comprehensive benchmark tests', async () => {
      const benchmarkTasks = [
        // Performance benchmark
        {
          id: 'performance-benchmark',
          type: ServiceType.OPTIMIZATION,
          expectedResponseTime: 50,
          expectedThroughput: 1000
        },
        // Memory benchmark
        {
          id: 'memory-benchmark',
          type: ServiceType.OPTIMIZATION,
          expectedMemoryReduction: 0.2,
          expectedPoolingEfficiency: 0.5
        },
        // Reliability benchmark
        {
          id: 'reliability-benchmark',
          type: ServiceType.MONITORING,
          expectedUptime: 0.99,
          expectedErrorRate: 0.01
        }
      ];

      for (const benchmark of benchmarkTasks) {
        const task: ServiceTask = {
          id: benchmark.id,
          type: benchmark.type,
          specification: {
            requirements: `Execute ${benchmark.id} benchmark`,
            acceptance: ['Benchmark completed', 'Metrics within thresholds'],
            context: { benchmark: true, ...benchmark }
          },
          metadata: { priority: 1, estimatedDuration: 5000 }
        };

        const result = await serviceManager.executeTask(task);
        expect(result.success).toBe(true);
        
        if (result.performanceMetrics) {
          if (benchmark.expectedResponseTime) {
            expect(result.performanceMetrics.responseTime).toBeLessThan(benchmark.expectedResponseTime);
          }
          if (benchmark.expectedThroughput) {
            expect(result.performanceMetrics.throughput).toBeGreaterThan(benchmark.expectedThroughput);
          }
        }
      }
    });
  });

  describe('System Integration Health Check', () => {
    test('should validate complete system health', async () => {
      const healthServiceConfig: ServiceConfig = {
        id: 'system-health-service',
        type: ServiceType.MONITORING,
        config: {
          autoStart: true,
          healthCheckInterval: 1000,
          alertThreshold: 0.8
        },
        dependencies: []
      };

      await serviceManager.registerService(healthServiceConfig);

      // Health check for all registered services
      const allServices = await serviceRegistry.getAllServices();
      expect(allServices.length).toBeGreaterThan(0);

      for (const service of allServices) {
        const state = serviceRegistry.getServiceState(service.id);
        expect(state).toBeDefined();
        expect(['registered', 'running', 'stopped']).toContain(state?.status);
      }

      // Agent system health
      const agentState = agent.getState();
      expect(agentState.initialized).toBe(true);
      expect(agentState.averageQualityScore).toBeGreaterThanOrEqual(0);

      // Service registry integrity
      const registryIssues = serviceRegistry.validateRegistry();
      const errorIssues = registryIssues.filter(issue => issue.severity === 'error');
      expect(errorIssues.length).toBe(0);
    });

    test('should demonstrate end-to-end workflow', async () => {
      // Complete workflow: Agent -> Service -> Validation
      
      // Step 1: Agent processes complex task
      const complexTask: AgentTask = {
        id: 'e2e-workflow-test',
        type: AgentTaskType.CODE_GENERATION,
        specification: {
          requirements: 'Generate and validate complete feature implementation',
          acceptance: [
            'Code generated with tests',
            'Service integration verified',
            'Quality metrics met',
            'TypeScript compliance confirmed'
          ],
          context: {
            featureType: 'full-stack',
            includeTests: true,
            includeValidation: true
          }
        },
        metadata: { priority: 1, estimatedComplexity: 0.8 }
      };

      const agentWorkflowResult = await agent.processTask(complexTask);
      expect(agentWorkflowResult.success).toBe(true);

      // Step 2: Service processes related infrastructure
      const infraTask: ServiceTask = {
        id: 'e2e-infrastructure-setup',
        type: ServiceType.CONTAINER,
        specification: {
          requirements: 'Set up infrastructure for generated code',
          acceptance: ['Container deployed', 'Services configured', 'Health checks passed'],
          context: {
            relatedAgentTask: complexTask.id,
            deploymentTarget: 'integration-test'
          }
        },
        metadata: { priority: 1, estimatedDuration: 8000 }
      };

      const serviceWorkflowResult = await serviceManager.executeTask(infraTask);
      expect(serviceWorkflowResult.success).toBe(true);

      // Step 3: Final validation
      expect(agentWorkflowResult.validation.typeScriptCompliant).toBe(true);
      expect(serviceWorkflowResult.containerResult?.status).toBe('running');
      expect(agentWorkflowResult.artifacts.length).toBeGreaterThan(0);
      expect(serviceWorkflowResult.performanceMetrics).toBeDefined();

      // Workflow completion metrics
      expect(agentWorkflowResult.validation.errorCount).toBe(0);
      expect(serviceWorkflowResult.containerResult?.exitCode).toBe(0);
    });
  });
});
