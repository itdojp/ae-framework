/**
 * Test for BaseAgent security improvements - Phase 1.2
 * Validates safe validation flow and error handling
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { BaseAgent, AgentOutput } from '../../src/agents/base-agent';
import { ValidationResult } from '../../src/cli/types';
import { PhaseType } from '../../src/utils/phase-state-manager';

// Test implementation of BaseAgent
class TestAgent extends BaseAgent {
  constructor() {
    super('intent' as PhaseType);
  }

  // Test public methods by exposing protected ones
  public async testValidateOutput(output: AgentOutput): Promise<ValidationResult> {
    return this.validateOutput(output);
  }

  public async testValidateDefault(output: AgentOutput): Promise<ValidationResult> {
    return this.validate(output);
  }
}

// Test agent with custom validation that always fails
class FailingValidationAgent extends BaseAgent {
  constructor() {
    super('test' as PhaseType);
  }

  protected async validate(output: AgentOutput): Promise<ValidationResult> {
    return {
      success: false,
      message: 'Custom validation failed',
      details: [{
        check: 'custom_check',
        passed: false,
        message: 'This validation always fails'
      }]
    };
  }

  public async testValidateOutput(output: AgentOutput): Promise<ValidationResult> {
    return this.validateOutput(output);
  }
}

// Test agent with validation that throws exceptions
class ThrowingValidationAgent extends BaseAgent {
  constructor() {
    super('code' as PhaseType);
  }

  protected async validate(_output: AgentOutput): Promise<ValidationResult> {
    throw new Error('Validation method threw an exception');
  }

  public async testValidateOutput(output: AgentOutput): Promise<ValidationResult> {
    return this.validateOutput(output);
  }
}

describe('BaseAgent Security - Phase 1.2', () => {
  let testAgent: TestAgent;
  let failingAgent: FailingValidationAgent;
  let throwingAgent: ThrowingValidationAgent;

  const mockOutput: AgentOutput = {
    type: 'requirements',
    content: 'Test requirements content',
    artifacts: ['requirements.md', 'specifications.yaml'],
    metadata: {
      phase: 'intent',
      timestamp: new Date().toISOString()
    },
    quality: {
      score: 85,
      metrics: {
        completeness: 90,
        clarity: 80
      }
    }
  };

  beforeEach(() => {
    testAgent = new TestAgent();
    failingAgent = new FailingValidationAgent();
    throwingAgent = new ThrowingValidationAgent();
  });

  describe('Default Safe Validation', () => {
    it('should provide safe default validation that always passes', async () => {
      const result = await testAgent.testValidateDefault(mockOutput);
      
      expect(result.success).toBe(true);
      expect(result.message).toContain('Default validation passed');
      expect(result.details).toHaveLength(1);
      expect(result.details[0].check).toBe('default_validation');
      expect(result.details[0].passed).toBe(true);
    });

    it('should log validation activity when using validateOutput wrapper', async () => {
      const result = await testAgent.testValidateOutput(mockOutput);
      
      expect(result.success).toBe(true);
      // The wrapper should have logged the activity (we can't directly test the log, 
      // but we can verify the validation completed successfully)
    });
  });

  describe('Custom Validation Override', () => {
    it('should allow custom validation that fails safely', async () => {
      const result = await failingAgent.testValidateOutput(mockOutput);
      
      expect(result.success).toBe(false);
      expect(result.message).toBe('Custom validation failed');
      expect(result.details[0].check).toBe('custom_check');
      expect(result.details[0].passed).toBe(false);
    });
  });

  describe('Exception Handling Safety', () => {
    it('should handle validation exceptions safely and not crash', async () => {
      const result = await throwingAgent.testValidateOutput(mockOutput);
      
      expect(result.success).toBe(false);
      expect(result.message).toContain('Validation error: Validation method threw an exception');
      expect(result.details).toHaveLength(1);
      expect(result.details[0].check).toBe('validation_error_handler');
      expect(result.details[0].passed).toBe(false);
      expect(result.details[0].message).toContain('failing safely');
    });

    it('should not throw exceptions even when validation fails catastrophically', async () => {
      await expect(throwingAgent.testValidateOutput(mockOutput)).resolves.toBeDefined();
    });
  });

  describe('AgentOutput Interface', () => {
    it('should accept different output types', async () => {
      const outputs: AgentOutput[] = [
        { ...mockOutput, type: 'requirements' },
        { ...mockOutput, type: 'specifications' },
        { ...mockOutput, type: 'tests' },
        { ...mockOutput, type: 'code' },
        { ...mockOutput, type: 'verification' },
        { ...mockOutput, type: 'deployment' },
        { ...mockOutput, type: 'generic' }
      ];

      for (const output of outputs) {
        const result = await testAgent.testValidateOutput(output);
        expect(result.success).toBe(true);
      }
    });

    it('should handle minimal output structure', async () => {
      const minimalOutput: AgentOutput = {
        type: 'generic',
        content: 'minimal content',
        artifacts: []
      };

      const result = await testAgent.testValidateOutput(minimalOutput);
      expect(result.success).toBe(true);
    });

    it('should handle output with quality metrics', async () => {
      const outputWithQuality: AgentOutput = {
        type: 'code',
        content: 'Generated code',
        artifacts: ['main.ts', 'test.ts'],
        quality: {
          score: 92,
          metrics: {
            complexity: 15,
            coverage: 95,
            maintainability: 88
          }
        }
      };

      const result = await testAgent.testValidateOutput(outputWithQuality);
      expect(result.success).toBe(true);
    });
  });
});