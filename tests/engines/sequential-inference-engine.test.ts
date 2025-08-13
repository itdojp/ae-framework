import { describe, test, expect, beforeEach, vi } from 'vitest';
import { SequentialInferenceEngine } from '../../src/engines/sequential-inference-engine.js';
import type { 
  ComplexQuery, 
  ProjectContext, 
  ChangeSet, 
  FileChange 
} from '../../src/engines/sequential-inference-engine.js';

describe('SequentialInferenceEngine', () => {
  let engine: SequentialInferenceEngine;

  beforeEach(() => {
    engine = new SequentialInferenceEngine({
      maxConcurrentQueries: 3,
      cacheSize: 50,
      timeoutMs: 10000,
      enableProfiling: true
    });
  });

  describe('processComplexQuery', () => {
    test('should process a simple query successfully', async () => {
      const query: ComplexQuery = {
        id: 'test-query-1',
        description: 'Analyze test data patterns',
        context: { 
          testData: [1, 2, 3, 4, 5],
          domain: 'testing' 
        },
        constraints: [],
        priority: 'medium'
      };

      const result = await engine.processComplexQuery(query);

      expect(result).toBeDefined();
      expect(result.queryId).toBe('test-query-1');
      expect(result.success).toBe(true);
      expect(result.steps).toHaveLength(3); // analyze, validate, synthesize
      expect(result.completedSteps).toBeGreaterThan(0);
      expect(result.confidence).toBeGreaterThan(0);
      expect(result.metadata.startTime).toBeInstanceOf(Date);
      expect(result.metadata.endTime).toBeInstanceOf(Date);
      expect(result.metadata.duration).toBeGreaterThan(0);
    });

    test('should handle queries with constraints', async () => {
      const query: ComplexQuery = {
        id: 'constrained-query',
        description: 'Process data with constraints',
        context: { data: { items: [1, 2, 3] } },
        constraints: [
          {
            type: 'logical',
            condition: 'items.length > 0',
            severity: 'error'
          }
        ],
        priority: 'high'
      };

      const result = await engine.processComplexQuery(query);

      expect(result.success).toBe(true);
      expect(result.steps.some(s => s.id.includes('validate'))).toBe(true);
    });

    test('should handle multiple concurrent queries', async () => {
      const queries: ComplexQuery[] = Array.from({ length: 3 }, (_, i) => ({
        id: `concurrent-query-${i}`,
        description: `Concurrent query ${i}`,
        context: { data: i, domain: 'concurrent' },
        constraints: [],
        priority: 'medium'
      }));

      const results = await Promise.all(
        queries.map(query => engine.processComplexQuery(query))
      );

      expect(results).toHaveLength(3);
      results.forEach((result, i) => {
        expect(result.queryId).toBe(`concurrent-query-${i}`);
        expect(result.success).toBe(true);
      });
    });

    test('should handle query with missing context gracefully', async () => {
      const query: ComplexQuery = {
        id: 'incomplete-query',
        description: 'Query with minimal context',
        context: {},
        constraints: [],
        priority: 'low'
      };

      const result = await engine.processComplexQuery(query);

      expect(result).toBeDefined();
      expect(result.queryId).toBe('incomplete-query');
      // Should still attempt processing even with minimal context
    });
  });

  describe('analyzeDeepDependencies', () => {
    test('should analyze project dependencies', async () => {
      const context: ProjectContext = {
        projectRoot: '/test/project',
        sourceFiles: [
          '/test/project/src/main.ts',
          '/test/project/src/utils.ts',
          '/test/project/src/types.ts'
        ],
        dependencies: {
          'express': '^4.18.0',
          'lodash': '^4.17.21'
        },
        devDependencies: {
          'typescript': '^4.9.0',
          'vitest': '^0.25.0'
        },
        packageJson: {
          name: 'test-project',
          version: '1.0.0'
        }
      };

      const result = await engine.analyzeDeepDependencies(context);

      expect(result).toBeDefined();
      expect(result.nodes).toBeInstanceOf(Array);
      expect(result.edges).toBeInstanceOf(Array);
      expect(result.cycles).toBeInstanceOf(Array);
      expect(result.criticalPaths).toBeInstanceOf(Array);
      expect(result.metrics).toBeDefined();
      expect(result.metrics.totalNodes).toBe(context.sourceFiles.length);
      expect(result.metrics.totalEdges).toBeGreaterThanOrEqual(0);
    });

    test('should handle empty project context', async () => {
      const context: ProjectContext = {
        projectRoot: '/empty/project',
        sourceFiles: [],
        dependencies: {},
        devDependencies: {}
      };

      const result = await engine.analyzeDeepDependencies(context);

      expect(result.nodes).toHaveLength(0);
      expect(result.edges).toHaveLength(0);
      expect(result.metrics.totalNodes).toBe(0);
    });
  });

  describe('evaluateImpactScope', () => {
    test('should evaluate impact of file changes', async () => {
      const changes: ChangeSet = {
        id: 'changeset-1',
        description: 'Update main components',
        files: [
          {
            path: '/src/main.ts',
            type: 'modify',
            lines: { added: 10, removed: 5, modified: 3 }
          },
          {
            path: '/src/new-feature.ts',
            type: 'create',
            content: 'export function newFeature() { return true; }'
          }
        ],
        timestamp: new Date(),
        author: 'test-user'
      };

      const result = await engine.evaluateImpactScope(changes);

      expect(result).toBeDefined();
      expect(result.changeSetId).toBe('changeset-1');
      expect(result.affectedComponents).toBeInstanceOf(Array);
      expect(result.affectedComponents.length).toBeGreaterThan(0);
      expect(result.riskLevel).toMatch(/^(low|medium|high|critical)$/);
      expect(result.estimatedEffort).toBeGreaterThan(0);
      expect(result.recommendations).toBeInstanceOf(Array);
      expect(result.testingRequirements).toBeInstanceOf(Array);
      expect(result.rollbackPlan).toBeInstanceOf(Array);
    });

    test('should calculate higher risk for many changes', async () => {
      const manyChanges: ChangeSet = {
        id: 'large-changeset',
        description: 'Major refactoring',
        files: Array.from({ length: 15 }, (_, i) => ({
          path: `/src/file${i}.ts`,
          type: 'modify' as const,
          lines: { added: 20, removed: 10, modified: 5 }
        })),
        timestamp: new Date(),
        author: 'test-user'
      };

      const result = await engine.evaluateImpactScope(manyChanges);

      expect(result.riskLevel).toMatch(/^(high|critical)$/);
      expect(result.estimatedEffort).toBeGreaterThan(20);
      expect(result.recommendations).toContain('Perform thorough testing');
    });

    test('should handle deletion changes', async () => {
      const deletionChanges: ChangeSet = {
        id: 'deletion-changeset',
        description: 'Remove deprecated files',
        files: [
          {
            path: '/src/deprecated.ts',
            type: 'delete'
          },
          {
            path: '/src/old-utils.ts',
            type: 'delete'
          }
        ],
        timestamp: new Date(),
        author: 'test-user'
      };

      const result = await engine.evaluateImpactScope(deletionChanges);

      expect(result.affectedComponents).toHaveLength(2);
      expect(result.rollbackPlan).toContain('Create backup of affected files');
    });
  });

  describe('event handling', () => {
    test('should emit events during query processing', async () => {
      const events: string[] = [];
      
      engine.on('queryStart', () => events.push('queryStart'));
      engine.on('stepStart', () => events.push('stepStart'));
      engine.on('stepComplete', () => events.push('stepComplete'));
      engine.on('queryComplete', () => events.push('queryComplete'));

      const query: ComplexQuery = {
        id: 'event-test-query',
        description: 'Test event emission',
        context: { data: 'test' },
        constraints: [],
        priority: 'medium'
      };

      await engine.processComplexQuery(query);

      expect(events).toContain('queryStart');
      expect(events).toContain('queryComplete');
      expect(events.filter(e => e === 'stepStart').length).toBeGreaterThan(0);
      expect(events.filter(e => e === 'stepComplete').length).toBeGreaterThan(0);
    });

    test('should emit error events on failure', async () => {
      const errors: any[] = [];
      
      engine.on('queryError', (error) => errors.push(error));
      engine.on('stepError', (error) => errors.push(error));

      // Create a problematic query that might cause errors
      const problematicQuery: ComplexQuery = {
        id: 'problematic-query',
        description: 'Query that might fail',
        context: null as any, // This might cause issues
        constraints: [],
        priority: 'critical'
      };

      try {
        await engine.processComplexQuery(problematicQuery);
      } catch (error) {
        // Expected to fail
      }

      // Should have emitted some error events
      expect(errors.length).toBeGreaterThan(0);
    });
  });

  describe('performance and memory', () => {
    test('should track memory usage in results', async () => {
      const query: ComplexQuery = {
        id: 'memory-test-query',
        description: 'Test memory tracking',
        context: { 
          largeData: Array.from({ length: 1000 }, (_, i) => ({ id: i, data: `item-${i}` }))
        },
        constraints: [],
        priority: 'medium'
      };

      const result = await engine.processComplexQuery(query);

      expect(result.metadata.memoryUsed).toBeGreaterThanOrEqual(0);
    });

    test('should handle timeout appropriately', async () => {
      const shortTimeoutEngine = new SequentialInferenceEngine({
        timeoutMs: 100 // Very short timeout
      });

      const query: ComplexQuery = {
        id: 'timeout-test-query',
        description: 'Query that should timeout',
        context: { data: 'test' },
        constraints: [],
        priority: 'medium'
      };

      // Mock a slow step handler to cause timeout
      const originalHandler = (shortTimeoutEngine as any).handleAnalyzeStep;
      (shortTimeoutEngine as any).handleAnalyzeStep = async () => {
        await new Promise(resolve => setTimeout(resolve, 200));
        return originalHandler.call(shortTimeoutEngine);
      };

      const result = await shortTimeoutEngine.processComplexQuery(query);
      
      // Should complete but might have some steps failed due to timeout handling
      expect(result).toBeDefined();
    });
  });
});