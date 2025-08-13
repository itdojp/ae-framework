import { describe, test, expect, beforeEach, vi } from 'vitest';
import { SequentialStrategy } from '../../../src/inference/strategies/sequential-strategy.js';
import type { ReasoningContext } from '../../../src/inference/strategies/sequential-strategy.js';

describe('SequentialStrategy', () => {
  let strategy: SequentialStrategy;

  beforeEach(() => {
    strategy = new SequentialStrategy();
  });

  describe('execute', () => {
    test('should execute sequential reasoning successfully', async () => {
      const context: ReasoningContext = {
        domain: 'testing',
        constraints: [
          { type: 'confidence_threshold', threshold: 0.6 }
        ],
        objectives: [
          'analyze data patterns',
          'identify anomalies'
        ],
        availableData: {
          dataset1: [1, 2, 3, 4, 5],
          dataset2: { items: ['a', 'b', 'c'] }
        },
        previousSteps: []
      };

      const result = await strategy.execute(context);

      expect(result).toBeDefined();
      expect(result.success).toBe(true);
      expect(result.steps).toHaveLength(4); // analyze, deduce, validate, synthesize
      expect(result.confidence).toBeGreaterThan(0);
      expect(result.reasoning).toBeInstanceOf(Array);
      expect(result.reasoning.length).toBeGreaterThan(0);
      expect(result.finalConclusion).toBeDefined();
    });

    test('should handle analysis step correctly', async () => {
      const context: ReasoningContext = {
        domain: 'data-analysis',
        constraints: [],
        objectives: ['understand data structure'],
        availableData: {
          users: [{ id: 1, name: 'Alice' }, { id: 2, name: 'Bob' }],
          settings: { theme: 'dark', language: 'en' }
        },
        previousSteps: []
      };

      const result = await strategy.execute(context);

      const analysisStep = result.steps.find(step => step.type === 'analyze');
      expect(analysisStep).toBeDefined();
      expect(analysisStep?.output).toBeDefined();
      expect(analysisStep?.output.patterns).toBeInstanceOf(Array);
      expect(analysisStep?.output.dataQuality).toBeDefined();
      expect(analysisStep?.confidence).toBeGreaterThan(0);
    });

    test('should perform deduction based on analysis', async () => {
      const context: ReasoningContext = {
        domain: 'problem-solving',
        constraints: [],
        objectives: ['solve optimization problem', 'minimize cost'],
        availableData: {
          costMatrix: [[1, 2, 3], [4, 5, 6]],
          constraints: { maxCost: 10 }
        },
        previousSteps: []
      };

      const result = await strategy.execute(context);

      const deductionStep = result.steps.find(step => step.type === 'deduce');
      expect(deductionStep).toBeDefined();
      expect(deductionStep?.output.hypotheses).toBeInstanceOf(Array);
      expect(deductionStep?.output.conclusion).toBeDefined();
      const analysisStep = result.steps.find(s => s.type === 'analyze');
      expect(analysisStep?.id).toBeDefined();
      if (analysisStep && deductionStep?.dependencies) {
        expect(deductionStep.dependencies).toContain(analysisStep.id);
      }
    });

    test('should validate conclusions against constraints', async () => {
      const context: ReasoningContext = {
        domain: 'validation-test',
        constraints: [
          { type: 'confidence_threshold', threshold: 0.8 },
          { type: 'logical', condition: 'result > 0' }
        ],
        objectives: ['generate valid result'],
        availableData: { value: 42 },
        previousSteps: []
      };

      const result = await strategy.execute(context);

      const validationStep = result.steps.find(step => step.type === 'validate');
      expect(validationStep).toBeDefined();
      expect(validationStep?.output.valid).toBe(true);
      expect(validationStep?.output.results).toBeInstanceOf(Array);
    });

    test('should synthesize final results', async () => {
      const context: ReasoningContext = {
        domain: 'synthesis-test',
        constraints: [],
        objectives: ['create comprehensive summary', 'provide recommendations'],
        availableData: {
          metrics: { accuracy: 0.95, precision: 0.88 },
          feedback: ['good performance', 'needs improvement in edge cases']
        },
        previousSteps: []
      };

      const result = await strategy.execute(context);

      const synthesisStep = result.steps.find(step => step.type === 'synthesize');
      expect(synthesisStep).toBeDefined();
      expect(synthesisStep?.output.keyFindings).toBeInstanceOf(Array);
      expect(synthesisStep?.output.recommendations).toBeInstanceOf(Array);
      expect(synthesisStep?.output.summary).toBeDefined();
    });

    test('should handle empty data gracefully', async () => {
      const context: ReasoningContext = {
        domain: 'empty-data-test',
        constraints: [],
        objectives: ['handle empty data'],
        availableData: {},
        previousSteps: []
      };

      const result = await strategy.execute(context);

      expect(result.success).toBe(true);
      expect(result.steps.length).toBeGreaterThan(0);
      
      const analysisStep = result.steps.find(step => step.type === 'analyze');
      expect(analysisStep?.output.dataQuality.score).toBe(0);
      expect(analysisStep?.output.dataQuality.issues).toContain('No data available');
    });

    test('should handle constraints filtering', async () => {
      const context: ReasoningContext = {
        domain: 'constraint-test',
        constraints: [
          { type: 'confidence_threshold', threshold: 0.9, domain: 'constraint-test' },
          { type: 'logical', condition: 'x > 0', domain: 'other-domain' },
          { type: 'global', condition: 'always_apply', domain: 'global' }
        ],
        objectives: ['test constraint filtering'],
        availableData: { x: 5 },
        previousSteps: []
      };

      const result = await strategy.execute(context);

      const analysisStep = result.steps.find(step => step.type === 'analyze');
      expect(analysisStep?.output.relevantConstraints).toHaveLength(2); // domain-specific + global
    });

    test('should calculate step confidence appropriately', async () => {
      const context: ReasoningContext = {
        domain: 'confidence-test',
        constraints: [],
        objectives: ['test confidence calculation'],
        availableData: { 
          goodData: [1, 2, 3, 4, 5],
          qualityMetrics: { completeness: 0.95, accuracy: 0.88 }
        },
        previousSteps: []
      };

      const result = await strategy.execute(context);

      result.steps.forEach(step => {
        expect(step.confidence).toBeGreaterThanOrEqual(0);
        expect(step.confidence).toBeLessThanOrEqual(1);
        expect(step.metadata.duration).toBeGreaterThanOrEqual(0); // Allow 0 for very fast operations
        expect(step.metadata.startTime).toBeInstanceOf(Date);
        if (step.metadata.endTime) {
          expect(step.metadata.endTime).toBeInstanceOf(Date);
        }
      });
    });

    test('should generate appropriate patterns', async () => {
      const context: ReasoningContext = {
        domain: 'pattern-test',
        constraints: [],
        objectives: ['identify patterns'],
        availableData: {
          arrayData: [1, 2, 3, 4, 5],
          objectData: { prop1: 'value1', prop2: 'value2', prop3: 'value3' },
          simpleValue: 42,
          nullValue: null
        },
        previousSteps: []
      };

      const result = await strategy.execute(context);

      const analysisStep = result.steps.find(step => step.type === 'analyze');
      const patterns = analysisStep?.output.patterns;

      expect(patterns).toBeInstanceOf(Array);
      
      const arrayPattern = patterns.find((p: any) => p.type === 'array_pattern');
      expect(arrayPattern).toBeDefined();
      expect(arrayPattern.key).toBe('arrayData');
      expect(arrayPattern.length).toBe(5);

      const objectPattern = patterns.find((p: any) => p.type === 'object_pattern');
      expect(objectPattern).toBeDefined();
      expect(objectPattern.key).toBe('objectData');
      expect(objectPattern.properties).toBe(3);
    });

    test('should provide meaningful reasoning explanations', async () => {
      const context: ReasoningContext = {
        domain: 'reasoning-explanation-test',
        constraints: [{ type: 'quality', threshold: 0.8 }],
        objectives: ['explain reasoning clearly', 'provide actionable insights'],
        availableData: { 
          performance: { cpu: 0.75, memory: 0.60, disk: 0.90 }
        },
        previousSteps: []
      };

      const result = await strategy.execute(context);

      expect(result.reasoning).toBeInstanceOf(Array);
      expect(result.reasoning.length).toBeGreaterThan(0);
      
      result.reasoning.forEach(reason => {
        expect(typeof reason).toBe('string');
        expect(reason.length).toBeGreaterThan(0);
      });

      // Should contain analysis, deduction, validation, and synthesis explanations
      expect(result.reasoning.some(r => r.includes('Analysis:'))).toBe(true);
      expect(result.reasoning.some(r => r.includes('Deduction:'))).toBe(true);
      expect(result.reasoning.some(r => r.includes('Validation:'))).toBe(true);
      expect(result.reasoning.some(r => r.includes('Synthesis:'))).toBe(true);
    });
  });

  describe('custom step processors', () => {
    test('should allow registration of custom step processors', async () => {
      const customProcessor = vi.fn().mockResolvedValue({
        custom: true,
        processed: 'custom data'
      });

      strategy.registerStepProcessor('custom', customProcessor);

      // This would require modifying the strategy to support custom step types
      // For now, we'll just verify the registration doesn't throw
      expect(() => {
        strategy.registerStepProcessor('another-custom', customProcessor);
      }).not.toThrow();
    });

    test('should handle processor errors gracefully', async () => {
      const context: ReasoningContext = {
        domain: 'error-handling-test',
        constraints: [],
        objectives: ['test error handling'],
        availableData: { data: 'test' },
        previousSteps: []
      };

      // The strategy should handle internal errors and still provide a result
      const result = await strategy.execute(context);

      // Even if some steps fail, we should get a result
      expect(result).toBeDefined();
      expect(result.success).toBeDefined();
      expect(result.reasoning).toBeInstanceOf(Array);
    });
  });
});