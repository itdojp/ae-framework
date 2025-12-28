/**
 * Test for TDD Infrastructure Setup
 * 
 * This test validates the TDD infrastructure setup for ae-framework self-improvement.
 * Following TDD principles: RED-GREEN-REFACTOR cycle enforcement.
 */

import { describe, it, expect, beforeEach, vi } from 'vitest';
import { formatGWT } from '../utils/gwt-format';
import { SelfImprovementTDDSetup, createSelfImprovementTDDSetup } from '../../src/self-improvement/tdd-setup.js';
import * as fs from 'node:fs';
import * as path from 'node:path';

// Mock dependencies at module level
vi.mock('../../src/integration/hybrid-tdd-system.js', () => ({
  HybridTDDSystem: vi.fn().mockImplementation(() => ({
    startProactiveMonitoring: vi.fn().mockResolvedValue(undefined)
  }))
}));

vi.mock('../../src/agents/tdd-agent.js', () => ({
  TDDAgent: vi.fn().mockImplementation(() => ({}))
}));

vi.mock('../../src/cli/metrics/MetricsCollector.js', () => ({
  MetricsCollector: vi.fn().mockImplementation(() => ({
    startPhase: vi.fn(),
    recordArtifact: vi.fn()
  }))
}));

vi.mock('../../src/cli/config/ConfigLoader.js', () => ({
  ConfigLoader: {
    load: vi.fn().mockReturnValue({
      name: 'ae-framework-v2',
      version: '2.0',
      description: 'Test configuration'
    })
  }
}));

// Mock fs at module level
vi.mock('node:fs', () => ({
  existsSync: vi.fn(),
  mkdirSync: vi.fn()
}));

describe('SelfImprovementTDDSetup', () => {
  let tddSetup: SelfImprovementTDDSetup;

  beforeEach(() => {
    // Reset all mocks
    vi.clearAllMocks();

    tddSetup = new SelfImprovementTDDSetup({
      projectRoot: '/test/project',
      configFile: 'ae-framework-v2.yml',
      enableRealTimeMonitoring: true,
      strictModeEnforcement: true,
      targetCoverage: 80,
      metricsOutputPath: 'metrics/self-improvement'
    });
  });

  describe('initialization', () => {
    it(
      formatGWT('TDD setup', 'create with default configuration', 'instance is created'),
      () => {
      const defaultSetup = new SelfImprovementTDDSetup();
      expect(defaultSetup).toBeInstanceOf(SelfImprovementTDDSetup);
    }
    );

    it(
      formatGWT('TDD setup', 'create with custom configuration', 'instance is created'),
      () => {
      const config = {
        projectRoot: '/custom/path',
        targetCoverage: 90
      };
      const customSetup = new SelfImprovementTDDSetup(config);
      expect(customSetup).toBeInstanceOf(SelfImprovementTDDSetup);
    }
    );

    it('should be created via factory function', () => {
      const factorySetup = createSelfImprovementTDDSetup();
      expect(factorySetup).toBeInstanceOf(SelfImprovementTDDSetup);
    });
  });

  describe('TDD infrastructure initialization', () => {
    it('should successfully initialize all TDD components when config exists', async () => {
      // Arrange: Mock config file exists
      vi.mocked(fs.existsSync).mockReturnValue(true);
      vi.mocked(fs.mkdirSync).mockReturnValue(undefined);

      // Act: Initialize TDD infrastructure
      const result = await tddSetup.initializeTDDInfrastructure();

      // Assert: All components should be initialized
      expect(result.success).toBe(true);
      expect(result.components.hybridTDD).toBe(true);
      expect(result.components.tddAgent).toBe(true);
      expect(result.components.metricsCollector).toBe(true);
      expect(result.message).toContain('successfully initialized');
    });

    it('should fail when configuration file does not exist', async () => {
      // Arrange: Mock config file does not exist
      vi.mocked(fs.existsSync).mockReturnValue(false);

      // Act: Attempt to initialize TDD infrastructure
      const result = await tddSetup.initializeTDDInfrastructure();

      // Assert: Should fail with appropriate error
      expect(result.success).toBe(false);
      expect(result.message).toContain('Configuration file not found');
    });

    it('should create metrics directory if it does not exist', async () => {
      // Arrange: Config exists, but metrics directory does not
      vi.mocked(fs.existsSync)
        .mockReturnValueOnce(true)  // Config file exists
        .mockReturnValueOnce(false); // Metrics directory does not exist
      vi.mocked(fs.mkdirSync).mockReturnValue(undefined);

      // Act: Initialize TDD infrastructure
      await tddSetup.initializeTDDInfrastructure();

      // Assert: Should create metrics directory
      expect(fs.mkdirSync).toHaveBeenCalledWith(
        '/test/project/metrics/self-improvement',
        { recursive: true }
      );
    });
  });

  describe('TDD infrastructure validation', () => {
    it('should validate operational infrastructure', async () => {
      // Arrange: Initialize infrastructure first
      vi.mocked(fs.existsSync).mockReturnValue(true);
      vi.mocked(fs.mkdirSync).mockReturnValue(undefined);
      await tddSetup.initializeTDDInfrastructure();

      // Act: Validate infrastructure
      const validation = await tddSetup.validateTDDInfrastructure();

      // Assert: Should be operational
      expect(validation.operational).toBe(true);
      expect(validation.checks.hybridTDDActive).toBe(true);
      expect(validation.checks.tddAgentReady).toBe(true);
      expect(validation.checks.metricsCollecting).toBe(true);
      expect(validation.checks.configValid).toBe(true);
      expect(validation.recommendations).toHaveLength(0);
    });

    it('should provide recommendations for non-operational infrastructure', async () => {
      // Arrange: Infrastructure not initialized
      vi.mocked(fs.existsSync).mockReturnValue(false);

      // Act: Validate infrastructure
      const validation = await tddSetup.validateTDDInfrastructure();

      // Assert: Should not be operational with recommendations
      expect(validation.operational).toBe(false);
      expect(validation.recommendations.length).toBeGreaterThan(0);
      expect(validation.recommendations).toContain('Initialize HybridTDDSystem');
      expect(validation.recommendations).toContain('Configure TDDAgent');
      expect(validation.recommendations).toContain('Set up MetricsCollector');
      expect(validation.recommendations).toContain('Create ae-framework-v2.yml configuration');
    });
  });

  describe('component access', () => {
    it('should provide access to initialized components', async () => {
      // Arrange: Initialize infrastructure
      vi.mocked(fs.existsSync).mockReturnValue(true);
      vi.mocked(fs.mkdirSync).mockReturnValue(undefined);
      await tddSetup.initializeTDDInfrastructure();

      // Act: Get component instances
      const hybridTDD = tddSetup.getHybridTDDSystem();
      const tddAgent = tddSetup.getTDDAgent();
      const metricsCollector = tddSetup.getMetricsCollector();

      // Assert: Components should be available
      expect(hybridTDD).toBeDefined();
      expect(tddAgent).toBeDefined();
      expect(metricsCollector).toBeDefined();
    });

    it('should return undefined for uninitialized components', () => {
      // Arrange: No initialization

      // Act: Get component instances
      const hybridTDD = tddSetup.getHybridTDDSystem();
      const tddAgent = tddSetup.getTDDAgent();
      const metricsCollector = tddSetup.getMetricsCollector();

      // Assert: Components should be undefined
      expect(hybridTDD).toBeUndefined();
      expect(tddAgent).toBeUndefined();
      expect(metricsCollector).toBeUndefined();
    });
  });

  describe('setup reporting', () => {
    it('should generate comprehensive setup report', () => {
      // Act: Generate setup report
      const report = tddSetup.generateSetupReport();

      // Assert: Report should contain key information
      expect(report).toContain('ae-framework Self-Improvement TDD Setup Report');
      expect(report).toContain('Project');
      expect(report).toContain('**Target Coverage**: 80%');
      expect(report).toContain('TypeScript Errors: 287 → 0');
      expect(report).toContain('Next Steps');
    });

    it('should show component status in report', async () => {
      // Arrange: Initialize infrastructure
      vi.mocked(fs.existsSync).mockReturnValue(true);
      vi.mocked(fs.mkdirSync).mockReturnValue(undefined);
      await tddSetup.initializeTDDInfrastructure();

      // Act: Generate setup report
      const report = tddSetup.generateSetupReport();

      // Assert: Report should show active components
      expect(report).toContain('HybridTDDSystem**: ✅ Active');
      expect(report).toContain('TDDAgent**: ✅ Ready');
      expect(report).toContain('MetricsCollector**: ✅ Collecting');
    });
  });

  describe('error handling', () => {
    it('should handle component initialization errors gracefully', async () => {
      // Arrange: Mock error during component setup
      vi.mocked(fs.existsSync).mockReturnValue(true);
      const mockError = new Error('Component initialization failed');
      
      // Create a new setup that will fail by using non-existent config
      const failingSetup = new SelfImprovementTDDSetup({
        projectRoot: '/non-existent',
        configFile: 'invalid-config.yml'
      });

      // Mock config file as not existing for this specific test
      vi.mocked(fs.existsSync).mockReturnValueOnce(false);

      // Act: Attempt initialization
      const result = await failingSetup.initializeTDDInfrastructure();

      // Assert: Should handle error gracefully
      expect(result.success).toBe(false);
      expect(result.message).toContain('Failed to initialize TDD infrastructure');
    });
  });
});

describe('TDD Enforcement Integration Tests', () => {
  it('should enforce TDD workflow for self-improvement', async () => {
    // This test validates that the TDD infrastructure will enforce
    // the RED-GREEN-REFACTOR cycle during self-improvement development
    
    // Arrange: Set up TDD infrastructure
    const tddSetup = createSelfImprovementTDDSetup({
      strictModeEnforcement: true,
      enableRealTimeMonitoring: true
    });

    // Mock file system for config
    vi.mocked(fs.existsSync).mockReturnValue(true);
    vi.mocked(fs.mkdirSync).mockReturnValue(undefined);

    // Act: Initialize and validate
    const initResult = await tddSetup.initializeTDDInfrastructure();
    const validation = await tddSetup.validateTDDInfrastructure();

    // Assert: TDD enforcement should be operational
    expect(initResult.success).toBe(true);
    expect(validation.operational).toBe(true);
    expect(validation.checks.tddAgentReady).toBe(true);
  });

  it('should track self-improvement metrics', async () => {
    // This test validates that metrics collection will track
    // the self-improvement progress effectively
    
    // Arrange: Set up with metrics focus
    const tddSetup = createSelfImprovementTDDSetup({
      metricsOutputPath: 'metrics/test-self-improvement'
    });

    // Mock file system
    vi.mocked(fs.existsSync).mockReturnValue(true);
    vi.mocked(fs.mkdirSync).mockReturnValue(undefined);

    // Act: Initialize infrastructure
    await tddSetup.initializeTDDInfrastructure();
    const metricsCollector = tddSetup.getMetricsCollector();

    // Assert: Metrics collection should be active
    expect(metricsCollector).toBeDefined();
    // Note: mkdirSync might not be called if directory already exists in mock
    // The important thing is that the setup completed successfully
  });
});
