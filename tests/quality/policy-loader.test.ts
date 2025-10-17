/**
 * Quality Policy Loader Tests
 * Tests for centralized quality policy management
 */

import { describe, it, expect, beforeEach, afterEach, vi } from 'vitest';
import * as fs from 'fs';
import * as path from 'path';
import { fileURLToPath } from 'url';
import { QualityPolicyLoader, QualityGateResult } from '../../src/quality/policy-loader.js';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

// Mock quality policy for testing
const mockPolicy = {
  version: '1.0.0-test',
  lastUpdated: '2025-01-19T09:40:00Z',
  description: 'Test quality policy',
  environments: {
    development: {
      description: 'Development environment',
      enforcementLevel: 'warning' as const,
    },
    production: {
      description: 'Production environment',
      enforcementLevel: 'blocking' as const,
    },
  },
  qualityGates: {
    'test-gate': {
      name: 'Test Gate',
      description: 'A test quality gate',
      category: 'testing',
      enabled: true,
      thresholds: {
        development: {
          minScore: 70,
          maxViolations: 10,
          blockOnFail: false,
        },
        production: {
          minScore: 95,
          maxViolations: 0,
          blockOnFail: true,
        },
      },
      tools: ['vitest'],
      commands: {
        test: 'npm test',
        report: 'echo "test report"',
      },
    },
    'coverage-gate': {
      name: 'Coverage Gate',
      description: 'Code coverage validation',
      category: 'testing',
      enabled: true,
      thresholds: {
        development: {
          lines: 60,
          functions: 60,
          branches: 50,
          statements: 60,
          blockOnFail: false,
        },
        production: {
          lines: 90,
          functions: 85,
          branches: 80,
          statements: 90,
          blockOnFail: true,
        },
      },
      tools: ['vitest', 'nyc'],
      commands: {
        test: 'npm run coverage',
      },
    },
  },
  compositeGates: {
    minimal: {
      description: 'Minimal gates for development',
      gates: ['test-gate'],
      environments: ['development'],
    },
    full: {
      description: 'Full gates for production',
      gates: ['test-gate', 'coverage-gate'],
      environments: ['production'],
    },
  },
  integrations: {
    ci: {
      githubActions: {
        enabled: true,
        workflow: '.github/workflows/quality.yml',
        triggerOn: ['push'],
        parallelExecution: true,
      },
      preCommitHooks: {
        enabled: false,
        hooks: [],
        blocking: false,
      },
    },
    monitoring: {
      opentelemetry: {
        enabled: true,
        metricsPrefix: 'quality',
        tracingEnabled: true,
      },
      dashboards: {},
    },
  },
  notifications: {},
  reporting: {
    formats: ['json'],
    outputDirectory: 'reports/quality',
    retention: {
      days: 30,
      maxReports: 100,
    },
    aggregation: {
      enabled: true,
      interval: 'daily',
      metrics: ['pass_rate'],
    },
  },
};

describe('Quality Policy Loader', () => {
  let tempPolicyPath: string;
  let loader: QualityPolicyLoader;

  beforeEach(() => {
    // Create temporary policy file
    tempPolicyPath = path.join(__dirname, 'test-policy.json');
    fs.writeFileSync(tempPolicyPath, JSON.stringify(mockPolicy, null, 2));
    loader = new QualityPolicyLoader(tempPolicyPath);
  });

  afterEach(() => {
    // Clean up temporary file
    if (fs.existsSync(tempPolicyPath)) {
      fs.unlinkSync(tempPolicyPath);
    }
  });

  describe('Policy Loading', () => {
    it('should load valid policy from file', () => {
      const policy = loader.loadPolicy();
      
      expect(policy).toBeDefined();
      expect(policy.version).toBe('1.0.0-test');
      expect(policy.qualityGates).toHaveProperty('test-gate');
      expect(policy.environments).toHaveProperty('development');
    });

    it('should throw error for missing policy file', () => {
      const invalidLoader = new QualityPolicyLoader('/nonexistent/path.json');
      
      expect(() => {
        invalidLoader.loadPolicy();
      }).toThrow('Quality policy file not found');
    });

    it('should throw error for invalid JSON', () => {
      fs.writeFileSync(tempPolicyPath, 'invalid json');
      
      expect(() => {
        loader.loadPolicy();
      }).toThrow('Failed to load quality policy');
    });

    it('should cache loaded policy', () => {
      const policy1 = loader.loadPolicy();
      const policy2 = loader.loadPolicy();
      
      expect(policy1).toBe(policy2); // Same object reference
    });
  });

  describe('Gates for Environment', () => {
    it('should return gates for development environment', () => {
      const gates = loader.getGatesForEnvironment('development');
      
      expect(gates).toHaveLength(1);
      expect(gates[0].name).toBe('Test Gate');
    });

    it('should return gates for production environment', () => {
      const gates = loader.getGatesForEnvironment('production');
      
      expect(gates).toHaveLength(2);
      expect(gates.map(g => g.name)).toContain('Test Gate');
      expect(gates.map(g => g.name)).toContain('Coverage Gate');
    });

    it('should return all enabled gates for unknown environment', () => {
      const gates = loader.getGatesForEnvironment('unknown');
      
      expect(gates).toHaveLength(2); // All enabled gates
    });
  });

  describe('Threshold Management', () => {
    it('should get threshold for specific environment', () => {
      const threshold = loader.getThreshold('test-gate', 'development');
      
      expect(threshold.minScore).toBe(70);
      expect(threshold.maxViolations).toBe(10);
      expect(threshold.blockOnFail).toBe(false);
    });

    it('should get threshold for production environment', () => {
      const threshold = loader.getThreshold('test-gate', 'production');
      
      expect(threshold.minScore).toBe(95);
      expect(threshold.maxViolations).toBe(0);
      expect(threshold.blockOnFail).toBe(true);
    });

    it('should fallback to development threshold for unknown environment', () => {
      const threshold = loader.getThreshold('test-gate', 'unknown');
      
      expect(threshold.minScore).toBe(70); // Development values
    });

    it('should throw error for unknown gate', () => {
      expect(() => {
        loader.getThreshold('unknown-gate', 'development');
      }).toThrow("Quality gate 'unknown-gate' not found");
    });
  });

  describe('Blocking Behavior', () => {
    it('should block for production environment', () => {
      const shouldBlock = loader.shouldBlock('test-gate', 'production');
      expect(shouldBlock).toBe(true);
    });

    it('should not block for development environment', () => {
      const shouldBlock = loader.shouldBlock('test-gate', 'development');
      expect(shouldBlock).toBe(false);
    });

    it('should block based on gate threshold', () => {
      const shouldBlock = loader.shouldBlock('coverage-gate', 'production');
      expect(shouldBlock).toBe(true);
    });
  });

  describe('Environment Configuration', () => {
    it('should get environment configuration', () => {
      const config = loader.getEnvironmentConfig('development');
      
      expect(config.description).toBe('Development environment');
      expect(config.enforcementLevel).toBe('warning');
    });

    it('should fallback to development for unknown environment', () => {
      const config = loader.getEnvironmentConfig('unknown');
      
      expect(config.description).toBe('Development environment');
    });
  });

  describe('Gate Result Validation', () => {
    it('should validate passing gate result', () => {
      const result: Partial<QualityGateResult> = {
        score: 80,
        violations: [],
      };

      const validation = loader.validateGateResult('test-gate', result, 'development');
      
      expect(validation.passed).toBe(true);
      expect(validation.violations).toHaveLength(0);
    });

    it('should validate failing gate result', () => {
      const result: Partial<QualityGateResult> = {
        score: 50, // Below minimum 70
        violations: ['some error'],
      };

      const validation = loader.validateGateResult('test-gate', result, 'development');
      
      expect(validation.passed).toBe(false);
      expect(validation.violations).toContain('Score 50 below minimum 70');
    });

    it('should validate coverage thresholds', () => {
      const result: Partial<QualityGateResult> = {
        details: {
          lines: 50, // Below minimum 60
          functions: 70,
          branches: 40, // Below minimum 50
          statements: 65,
        },
        violations: [],
      };

      const validation = loader.validateGateResult('coverage-gate', result, 'development');
      
      expect(validation.passed).toBe(false);
      expect(validation.violations).toContain('Line coverage 50% below minimum 60%');
      expect(validation.violations).toContain('Branch coverage 40% below minimum 50%');
    });

    it('should validate violation count', () => {
      const result: Partial<QualityGateResult> = {
        score: 80,
        violations: new Array(15).fill('violation'), // More than maxViolations (10)
      };

      const validation = loader.validateGateResult('test-gate', result, 'development');
      
      expect(validation.passed).toBe(false);
      expect(validation.violations).toContain('Too many violations: 15 > 10');
    });
  });

  describe('Report Generation', () => {
    it('should generate quality report', () => {
      const results: QualityGateResult[] = [
        {
          gateKey: 'test-gate',
          gateName: 'test-gate',
          passed: true,
          score: 85,
          violations: [],
          executionTime: 1000,
          environment: 'development',
          threshold: loader.getThreshold('test-gate', 'development'),
        },
        {
          gateKey: 'coverage-gate',
          gateName: 'coverage-gate',
          passed: false,
          score: 55,
          violations: ['Coverage too low'],
          executionTime: 2000,
          environment: 'development',
          threshold: loader.getThreshold('coverage-gate', 'development'),
        },
      ];

      const report = loader.generateReport(results, 'development');
      
      expect(report.environment).toBe('development');
      expect(report.totalGates).toBe(2);
      expect(report.passedGates).toBe(1);
      expect(report.failedGates).toBe(1);
      expect(report.overallScore).toBe(70); // Average of 85 and 55
      expect(report.summary.executionTime).toBe(3000);
      expect(report.summary.byCategory.testing.total).toBe(2);
      expect(report.summary.byCategory.testing.passed).toBe(1);
    });

    it('should identify blockers in report', () => {
      const results: QualityGateResult[] = [
        {
          gateKey: 'test-gate',
          gateName: 'test-gate',
          passed: false,
          violations: ['Test failed'],
          executionTime: 1000,
          environment: 'production',
          threshold: loader.getThreshold('test-gate', 'production'),
        },
      ];

      const report = loader.generateReport(results, 'production');
      
      expect(report.summary.blockers).toContain('test-gate');
    });
  });

  describe('Policy Export', () => {
    it('should export policy as JSON', () => {
      const exported = loader.exportPolicy('json');
      const parsed = JSON.parse(exported);
      
      expect(parsed.version).toBe('1.0.0-test');
      expect(parsed.qualityGates).toHaveProperty('test-gate');
    });

    it('should export policy summary', () => {
      const summary = loader.exportPolicy('summary');
      
      expect(summary).toContain('Quality Policy Summary');
      expect(summary).toContain('Version: 1.0.0-test');
      expect(summary).toContain('Environments (2)');
      expect(summary).toContain('Quality Gates (2)');
    });
  });

  describe('Integration and Configuration', () => {
    it('should get integration settings', () => {
      const integrations = loader.getIntegrations();
      
      expect(integrations.ci.githubActions.enabled).toBe(true);
      expect(integrations.monitoring.opentelemetry.enabled).toBe(true);
    });

    it('should get reporting configuration', () => {
      const reporting = loader.getReportingConfig();
      
      expect(reporting.formats).toContain('json');
      expect(reporting.retention.days).toBe(30);
    });

    it('should get composite gate definition', () => {
      const compositeGate = loader.getCompositeGate('minimal');
      
      expect(compositeGate).toBeDefined();
      expect(compositeGate?.gates).toContain('test-gate');
      expect(compositeGate?.environments).toContain('development');
    });

    it('should return null for unknown composite gate', () => {
      const compositeGate = loader.getCompositeGate('unknown');
      expect(compositeGate).toBeNull();
    });
  });
});