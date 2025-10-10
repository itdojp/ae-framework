/**
 * Conformance Verification Engine Tests
 * Phase 2.2: Test suite for runtime conformance verification engine
 */

import { describe, it, expect, beforeEach, afterEach, vi } from 'vitest';
import { ConformanceVerificationEngine } from '../../src/conformance/verification-engine.js';
import { 
  ConformanceConfig, 
  ConformanceRule, 
  RuntimeContext,
  ConformanceRuleCategory,
  ViolationSeverity 
} from '../../src/conformance/types.js';

describe('ConformanceVerificationEngine', () => {
  let engine: ConformanceVerificationEngine;
  let config: ConformanceConfig;
  let context: RuntimeContext;

  beforeEach(() => {
    config = {
      enabled: true,
      mode: 'permissive',
      rules: [],
      sampling: {
        enabled: false,
        rate: 1.0,
        strategy: 'random'
      },
      performance: {
        timeoutMs: 5000,
        maxConcurrentChecks: 10,
        cacheResults: true,
        cacheTtlMs: 300000
      },
      reporting: {
        destinations: ['console'],
        batchSize: 100,
        flushIntervalMs: 30000
      },
      alerting: {
        enabled: false,
        thresholds: {},
        channels: []
      }
    };

    engine = new ConformanceVerificationEngine(config);
    
    context = {
      timestamp: new Date().toISOString(),
      executionId: 'test-execution-' + Date.now(),
      environment: 'test',
      version: '2.2.0',
      metadata: {
        test: true
      }
    };
  });

  afterEach(async () => {
    if (engine) {
      await engine.stop();
    }
  });

  describe('engine lifecycle', () => {
    it('should start and stop correctly', async () => {
      let startedEvent = false;
      let stoppedEvent = false;

      engine.on('started', () => { startedEvent = true; });
      engine.on('stopped', () => { stoppedEvent = true; });

      await engine.start();
      expect(startedEvent).toBe(true);

      await engine.stop();
      expect(stoppedEvent).toBe(true);
    });

    it('should throw error when starting already running engine', async () => {
      await engine.start();
      await expect(engine.start()).rejects.toThrow('already running');
    });

    it('should handle multiple stop calls gracefully', async () => {
      await engine.start();
      await engine.stop();
      await engine.stop(); // Should not throw
    });
  });

  describe('rule management', () => {
    it('should add and retrieve rules', async () => {
      const rule: ConformanceRule = createTestRule('data_validation', 'major');
      const initialCount = engine.getRules().length;
      
      await engine.addRule(rule);
      const rules = engine.getRules();
      
      expect(rules).toHaveLength(initialCount + 1);
      expect(rules.some(r => r.id === rule.id)).toBe(true);
    });

    it('should update existing rules', async () => {
      const rule: ConformanceRule = createTestRule('data_validation', 'major');
      await engine.addRule(rule);

      const updatedRule = { ...rule, name: 'Updated Rule' };
      await engine.updateRule(updatedRule);

      const rules = engine.getRules();
      const found = rules.find(r => r.id === rule.id);
      expect(found?.name).toBe('Updated Rule');
    });

    it('should remove rules', async () => {
      const rule: ConformanceRule = createTestRule('data_validation', 'major');
      await engine.addRule(rule);

      let ruleCount = engine.getRules().length;
      await engine.removeRule(rule.id);

      expect(engine.getRules().length).toBe(ruleCount - 1);
    });

    it('should get rules by category', async () => {
      const dataRule: ConformanceRule = createTestRule('data_validation', 'major');
      const apiRule: ConformanceRule = createTestRule('api_contract', 'minor');
      
      await engine.addRule(dataRule);
      await engine.addRule(apiRule);

      const dataRules = engine.getRulesByCategory('data_validation');
      const apiRules = engine.getRulesByCategory('api_contract');

      expect(dataRules.some(r => r.id === dataRule.id)).toBe(true);
      expect(apiRules.some(r => r.id === apiRule.id)).toBe(true);
    });

    it('should emit events for rule operations', async () => {
      let addedEvent = false;
      let updatedEvent = false;
      let removedEvent = false;

      engine.on('rule_added', () => { addedEvent = true; });
      engine.on('rule_updated', () => { updatedEvent = true; });
      engine.on('rule_removed', () => { removedEvent = true; });

      const rule: ConformanceRule = createTestRule('data_validation', 'major');
      
      await engine.addRule(rule);
      expect(addedEvent).toBe(true);

      await engine.updateRule({ ...rule, name: 'Updated' });
      expect(updatedEvent).toBe(true);

      await engine.removeRule(rule.id);
      expect(removedEvent).toBe(true);
    });
  });

  describe('verification process', () => {
    beforeEach(async () => {
      await engine.start();
    });

    it('should verify data against rules', async () => {
      const rule: ConformanceRule = createTestRule('data_validation', 'major', 'data.required');
      await engine.addRule(rule);

      const testData = { required: true, value: 'test' };
      const result = await engine.verify(testData, context);

      expect(result.overall).toBe('pass');
      expect(result.results.length).toBeGreaterThan(0);
      expect(result.summary.totalRules).toBeGreaterThan(0);
    });

    it('should detect violations', async () => {
      const rule: ConformanceRule = createTestRule('data_validation', 'major', 'data.missing');
      await engine.addRule(rule);

      const testData = { present: true };
      const result = await engine.verify(testData, context);

      expect(result.overall).toBe('fail');
      expect(result.violations.length).toBeGreaterThan(0);
    });

    it('updates metrics aggregates when violations occur', async () => {
      const rule: ConformanceRule = createTestRule('security_policy', 'major', 'data.isEncrypted === true');
      await engine.addRule(rule);

      const result = await engine.verify({ isEncrypted: false }, context);

      expect(result.overall).toBe('fail');
      expect(result.violations.length).toBeGreaterThan(0);

      const metrics = engine.getMetrics();
      expect(metrics.counts.totalVerifications).toBeGreaterThanOrEqual(1);
      expect(metrics.counts.totalViolations).toBeGreaterThan(0);
      expect(metrics.counts.uniqueViolations).toBeGreaterThanOrEqual(1);
      expect(metrics.topViolations[0]).toMatchObject({
        ruleId: rule.id,
        ruleName: rule.name,
        count: expect.any(Number),
        lastOccurrence: expect.any(String)
      });
      expect(metrics.violationTrends.some(trend =>
        trend.category === 'security_policy' && trend.severity === 'major' && trend.count >= 1
      )).toBe(true);
    });

    it('should handle verification errors gracefully', async () => {
      const rule: ConformanceRule = createTestRule('data_validation', 'major', 'invalid.expression.that.throws');
      await engine.addRule(rule);

      const result = await engine.verify({}, context);

      expect(result.overall).toBe('error');
      expect(result.results.some(r => r.status === 'error')).toBe(true);
    });

    it('should respect rule filtering', async () => {
      const rule1: ConformanceRule = createTestRule('data_validation', 'major');
      const rule2: ConformanceRule = createTestRule('api_contract', 'minor');
      
      await engine.addRule(rule1);
      await engine.addRule(rule2);

      const result = await engine.verify({}, context, { 
        ruleIds: [rule1.id] 
      });

      expect(result.results.some(r => r.ruleId === rule1.id)).toBe(true);
    });

    it('should skip specified categories', async () => {
      const rule1: ConformanceRule = createTestRule('data_validation', 'major');
      const rule2: ConformanceRule = createTestRule('api_contract', 'minor');
      
      await engine.addRule(rule1);
      await engine.addRule(rule2);

      const result = await engine.verify({}, context, { 
        skipCategories: ['api_contract'] 
      });

      expect(result.results.some(r => {
        const rule = engine.getRules().find(rule => rule.id === r.ruleId);
        return rule?.category === 'api_contract';
      })).toBe(false);
    });

    it('should emit verification events', async () => {
      let completedEvent = false;
      engine.on('verification_completed', () => { completedEvent = true; });

      const testData = { test: true };
      await engine.verify(testData, context);

      expect(completedEvent).toBe(true);
    });
  });

  describe('metrics collection', () => {
    beforeEach(async () => {
      await engine.start();
    });

    it('should track verification metrics', async () => {
      const initialMetrics = engine.getMetrics();
      
      const testData = { test: true };
      await engine.verify(testData, context);

      const updatedMetrics = engine.getMetrics();
      expect(updatedMetrics.counts.totalVerifications).toBeGreaterThan(
        initialMetrics.counts.totalVerifications
      );
    });

    it('should track violation metrics', async () => {
      const rule: ConformanceRule = createTestRule('data_validation', 'major', 'data.missing');
      await engine.addRule(rule);

      const initialMetrics = engine.getMetrics();
      
      const testData = { present: true }; // Missing required field
      await engine.verify(testData, context);

      const updatedMetrics = engine.getMetrics();
      expect(updatedMetrics.counts.totalViolations).toBeGreaterThan(
        initialMetrics.counts.totalViolations
      );
    });

    it('should reset metrics', async () => {
      const testData = { test: true };
      await engine.verify(testData, context);

      engine.resetMetrics();
      const metrics = engine.getMetrics();

      expect(metrics.counts.totalVerifications).toBe(0);
      expect(metrics.counts.totalViolations).toBe(0);
    });
  });

  describe('configuration management', () => {
    it('should get current configuration', () => {
      const currentConfig = engine.getConfig();
      expect(currentConfig.enabled).toBe(config.enabled);
      expect(currentConfig.mode).toBe(config.mode);
    });

    it('should update configuration', () => {
      const newConfig = { enabled: false, mode: 'strict' as const };
      engine.updateConfig(newConfig);

      const updatedConfig = engine.getConfig();
      expect(updatedConfig.enabled).toBe(false);
      expect(updatedConfig.mode).toBe('strict');
    });

    it('should emit config update events', () => {
      let configUpdated = false;
      engine.on('config_updated', () => { configUpdated = true; });

      engine.updateConfig({ enabled: false });
      expect(configUpdated).toBe(true);
    });
  });

  describe('monitor management', () => {
    it('should add and remove monitors', () => {
      const mockMonitor = createMockMonitor();
      
      let monitorAdded = false;
      let monitorRemoved = false;
      
      engine.on('monitor_added', () => { monitorAdded = true; });
      engine.on('monitor_removed', () => { monitorRemoved = true; });

      engine.addMonitor(mockMonitor);
      expect(monitorAdded).toBe(true);

      engine.removeMonitor(mockMonitor.id);
      expect(monitorRemoved).toBe(true);
    });
  });

  describe('error handling', () => {
    it('should handle verification when engine not running', async () => {
      // Engine not started
      await expect(engine.verify({}, context)).rejects.toThrow('not running');
    });

    it('should handle invalid rule data gracefully', async () => {
      const invalidRule = createTestRule('data_validation', 'major');
      // Make rule invalid by removing required fields
      delete (invalidRule as any).id;

      await expect(engine.addRule(invalidRule as any)).rejects.toThrow();
    });
  });

  describe('sampling configuration', () => {
    beforeEach(async () => {
      config.sampling = {
        enabled: true,
        rate: 0.5,
        strategy: 'random'
      };
      engine = new ConformanceVerificationEngine(config);
      await engine.start();
    });

    it('should apply sampling when enabled', async () => {
      // Add multiple rules
      for (let i = 0; i < 10; i++) {
        const rule: ConformanceRule = createTestRule('data_validation', 'major');
        await engine.addRule(rule);
      }

      const testData = { test: true };
      const result = await engine.verify(testData, context);

      // With 50% sampling, should execute fewer rules than total available
      expect(result.summary.rulesExecuted).toBeLessThan(engine.getRules().length);
    });
  });

  // Helper functions
  function createTestRule(
    category: ConformanceRuleCategory, 
    severity: ViolationSeverity,
    expression: string = 'true'
  ): ConformanceRule {
    return {
      id: generateTestUUID(),
      name: `Test ${category} Rule`,
      description: `Test rule for ${category}`,
      category,
      severity,
      enabled: true,
      condition: {
        expression,
        variables: ['data'],
        constraints: {}
      },
      actions: ['log_violation'],
      metadata: {
        createdAt: new Date().toISOString(),
        updatedAt: new Date().toISOString(),
        version: '1.0.0',
        tags: ['test']
      }
    };
  }

  function createMockMonitor() {
    return {
      id: 'test-monitor',
      name: 'Test Monitor',
      verify: vi.fn().mockResolvedValue({
        id: generateTestUUID(),
        ruleId: 'test-rule',
        status: 'pass',
        timestamp: new Date().toISOString(),
        duration: 100,
        context,
        metrics: { executionTime: 100 }
      }),
      canVerify: vi.fn().mockReturnValue(true),
      getRules: vi.fn().mockReturnValue([]),
      updateRule: vi.fn().mockResolvedValue(undefined),
      removeRule: vi.fn().mockResolvedValue(undefined)
    };
  }

  function generateTestUUID(): string {
    return 'test-uuid-' + Math.random().toString(36).substr(2, 9);
  }
});
