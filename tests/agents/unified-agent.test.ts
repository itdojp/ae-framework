/**
 * @fileoverview Unified Agent Architecture Tests
 * TDD-first implementation for Phase 2: Agent System Refactoring
 * Goal: Test-driven unification of all agents under a common domain model
 */

import { describe, test, expect, beforeEach } from 'vitest';
import { UnifiedAgent } from '../../src/agents/unified-agent.js';
import { AgentTask, TaskType, TaskResult } from '../../src/agents/domain-types.js';

describe('UnifiedAgent - Domain Model Architecture', () => {
  let agent: UnifiedAgent;

  beforeEach(async () => {
    agent = new UnifiedAgent({
      id: 'test-agent',
      type: 'code-generation',
      capabilities: ['typescript', 'testing', 'validation'],
      context: {
        projectRoot: '/test',
        phase: 'code',
        tddEnabled: true
      }
    });
  });

  describe('Core Domain Model', () => {
    test('should implement unified task processing interface', async () => {
      const task: AgentTask = {
        id: 'test-task-1',
        type: TaskType.CODE_GENERATION,
        specification: {
          requirements: 'Generate TypeScript class with strict typing',
          acceptance: ['Valid TypeScript syntax', 'Zero type errors'],
          context: { targetPath: 'src/test/example.ts' }
        },
        metadata: {
          priority: 1,
          estimatedComplexity: 0.5
        }
      };

      const result: TaskResult = await agent.processTask(task);

      expect(result.success).toBe(true);
      expect(result.taskId).toBe(task.id);
      expect(result.artifacts).toBeDefined();
      expect(result.artifacts.length).toBeGreaterThan(0);
      expect(result.validation).toBeDefined();
      expect(result.validation.typeScriptCompliant).toBe(true);
    });

    test('should enforce TDD workflow for all task types', async () => {
      const testTask: AgentTask = {
        id: 'tdd-task',
        type: TaskType.TEST_GENERATION,
        specification: {
          requirements: 'Generate tests before implementation',
          acceptance: ['Tests defined first', 'Red-Green-Refactor cycle'],
          context: { testFirst: true }
        },
        metadata: { priority: 1, estimatedComplexity: 0.3 }
      };

      const result = await agent.processTask(testTask);

      expect(result.success).toBe(true);
      expect(result.tddCompliance).toBeDefined();
      expect(result.tddCompliance.testsFirst).toBe(true);
      expect(result.tddCompliance.redPhaseCompleted).toBe(true);
    });

    test('should support all existing agent types through unified interface', async () => {
      const agentTypes = [
        'intent',
        'formal',
        'test-generation', 
        'code-generation',
        'verification',
        'validation',
        'container',
        'operate'
      ];

      for (const type of agentTypes) {
        const specializedAgent = new UnifiedAgent({
          id: `${type}-agent`,
          type,
          capabilities: ['typescript', 'domain-modeling'],
          context: { projectRoot: '/test', phase: 'code', tddEnabled: true }
        });

        expect(specializedAgent.getType()).toBe(type);
        expect(specializedAgent.getCapabilities()).toContain('domain-modeling');
      }
    });
  });

  describe('Quality Assurance', () => {
    test('should validate TypeScript compliance for all outputs', async () => {
      const task: AgentTask = {
        id: 'validation-test',
        type: TaskType.VALIDATION,
        specification: {
          requirements: 'Validate TypeScript strict mode compliance',
          acceptance: ['Zero type errors', 'Strict mode compatible'],
          context: { strictMode: true }
        },
        metadata: { priority: 1, estimatedComplexity: 0.4 }
      };

      const result = await agent.processTask(task);

      expect(result.success).toBe(true);
      expect(result.validation.typeScriptCompliant).toBe(true);
      expect(result.validation.strictModeCompatible).toBe(true);
      expect(result.validation.errorCount).toBe(0);
    });

    test('should enforce 80% test coverage threshold', async () => {
      const coverageTask: AgentTask = {
        id: 'coverage-test',
        type: TaskType.QUALITY_ASSURANCE,
        specification: {
          requirements: 'Ensure minimum 80% test coverage',
          acceptance: ['Coverage >= 80%', 'All branches tested'],
          context: { coverageThreshold: 0.8 }
        },
        metadata: { priority: 1, estimatedComplexity: 0.6 }
      };

      const result = await agent.processTask(coverageTask);

      expect(result.success).toBe(true);
      expect(result.metrics).toBeDefined();
      expect(result.metrics.testCoverage).toBeGreaterThanOrEqual(0.8);
    });
  });

  describe('Integration with Existing System', () => {
    test('should be compatible with PhaseStateManager', async () => {
      const context = agent.getContext();
      expect(context.phase).toBe('code');
      expect(context.tddEnabled).toBe(true);
      
      const capabilities = agent.getCapabilities();
      expect(capabilities).toContain('typescript');
      expect(capabilities).toContain('testing');
      expect(capabilities).toContain('validation');
    });

    test('should support phase transition validation', async () => {
      const transitionTask: AgentTask = {
        id: 'phase-transition',
        type: TaskType.PHASE_VALIDATION,
        specification: {
          requirements: 'Validate Phase 2 completion criteria',
          acceptance: ['All agents unified', 'TypeScript compliant'],
          context: { targetPhase: 'operate' }
        },
        metadata: { priority: 1, estimatedComplexity: 0.7 }
      };

      const result = await agent.processTask(transitionTask);

      expect(result.success).toBe(true);
      expect(result.phaseValidation).toBeDefined();
      expect(result.phaseValidation?.readyForNextPhase).toBe(true);
    });
  });
});

describe('Domain Types Integration', () => {
  test('should define comprehensive task type enumeration', () => {
    const expectedTypes = [
      TaskType.INTENT_ANALYSIS,
      TaskType.FORMAL_SPECIFICATION,
      TaskType.TEST_GENERATION,
      TaskType.CODE_GENERATION,
      TaskType.VERIFICATION,
      TaskType.VALIDATION,
      TaskType.DEPLOYMENT,
      TaskType.QUALITY_ASSURANCE,
      TaskType.PHASE_VALIDATION
    ];

    expectedTypes.forEach(type => {
      expect(Object.values(TaskType)).toContain(type);
    });
  });

  test('should enforce task specification structure', () => {
    const validTask: AgentTask = {
      id: 'structure-test',
      type: TaskType.CODE_GENERATION,
      specification: {
        requirements: 'Test specification structure',
        acceptance: ['Requirement met'],
        context: { testContext: true }
      },
      metadata: {
        priority: 1,
        estimatedComplexity: 0.1
      }
    };

    expect(validTask.id).toBeDefined();
    expect(validTask.type).toBeDefined();
    expect(validTask.specification.requirements).toBeDefined();
    expect(validTask.specification.acceptance).toBeInstanceOf(Array);
    expect(validTask.metadata.priority).toBeGreaterThan(0);
  });
});
