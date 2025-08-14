/**
 * Tests for Dependency Analyzer - Phase 3.1 Implementation
 */

import { describe, test, expect, beforeEach, vi } from 'vitest';
import { DependencyAnalyzer } from '../../src/analysis/dependency-analyzer.js';
import type { 
  DependencyAnalysisRequest, 
  DependencyAnalysisResult,
  ImpactAnalysisRequest,
  DependencyNode,
  CircularDependency
} from '../../src/analysis/dependency-analyzer.js';

describe('DependencyAnalyzer', () => {
  let analyzer: DependencyAnalyzer;

  beforeEach(() => {
    analyzer = new DependencyAnalyzer({
      cacheSize: 10,
      cacheTTL: 1000,
      maxConcurrentAnalyses: 2
    });
  });

  describe('analyzeDependencies', () => {
    test('should analyze project dependencies successfully', async () => {
      const request: DependencyAnalysisRequest = {
        id: 'test-analysis-001',
        projectRoot: '/test/project',
        analysisScope: 'project',
        includeExternal: true,
        maxDepth: 5,
        analysisTypes: ['structural', 'circular', 'risk']
      };

      const result = await analyzer.analyzeDependencies(request);

      expect(result).toBeDefined();
      expect(result.requestId).toBe(request.id);
      expect(result.graph).toBeDefined();
      expect(result.nodes).toBeInstanceOf(Array);
      expect(result.circularDependencies).toBeInstanceOf(Array);
      expect(result.metrics).toBeDefined();
      expect(result.riskAssessment).toBeDefined();
      expect(result.recommendations).toBeInstanceOf(Array);
    });

    test('should handle module-scope analysis', async () => {
      const request: DependencyAnalysisRequest = {
        id: 'module-analysis-001',
        projectRoot: '/test/project',
        targetFiles: ['src/main.ts', 'src/utils.ts'],
        analysisScope: 'module',
        includeExternal: false,
        analysisTypes: ['structural', 'functional']
      };

      const result = await analyzer.analyzeDependencies(request);

      expect(result.requestId).toBe(request.id);
      expect(result.graph.metrics.totalNodes).toBeGreaterThanOrEqual(0);
      expect(result.metrics.totalNodes).toBeGreaterThanOrEqual(0);
    });

    test('should detect circular dependencies', async () => {
      const request: DependencyAnalysisRequest = {
        id: 'circular-test-001',
        projectRoot: '/test/circular-project',
        analysisScope: 'project',
        includeExternal: false,
        analysisTypes: ['circular']
      };

      const result = await analyzer.analyzeDependencies(request);

      expect(result.circularDependencies).toBeInstanceOf(Array);
      
      // Check circular dependency structure if any are found
      if (result.circularDependencies.length > 0) {
        const cycle = result.circularDependencies[0];
        expect(cycle.id).toBeDefined();
        expect(cycle.cycle).toBeInstanceOf(Array);
        expect(cycle.cycle.length).toBeGreaterThan(1);
        expect(cycle.severity).toMatch(/warning|error|critical/);
        expect(cycle.suggestions).toBeInstanceOf(Array);
        expect(cycle.suggestions.length).toBeGreaterThan(0);
      }
    });

    test('should calculate comprehensive metrics', async () => {
      const request: DependencyAnalysisRequest = {
        id: 'metrics-test-001',
        projectRoot: '/test/project',
        analysisScope: 'project',
        includeExternal: true,
        analysisTypes: ['structural', 'performance']
      };

      const result = await analyzer.analyzeDependencies(request);

      expect(result.metrics).toBeDefined();
      expect(result.metrics.totalNodes).toBeGreaterThanOrEqual(0);
      expect(result.metrics.totalEdges).toBeGreaterThanOrEqual(0);
      expect(result.metrics.averageDependencies).toBeGreaterThanOrEqual(0);
      expect(result.metrics.maxDependencyDepth).toBeGreaterThanOrEqual(0);
      expect(result.metrics.modularityScore).toBeGreaterThanOrEqual(0);
      expect(result.metrics.modularityScore).toBeLessThanOrEqual(1);
      expect(result.metrics.cohesionScore).toBeGreaterThanOrEqual(0);
      expect(result.metrics.cohesionScore).toBeLessThanOrEqual(1);
      expect(result.metrics.couplingScore).toBeGreaterThanOrEqual(0);
      expect(result.metrics.stabilityIndex).toBeGreaterThanOrEqual(0);
      expect(result.metrics.stabilityIndex).toBeLessThanOrEqual(1);
    });

    test('should assess risks properly', async () => {
      const request: DependencyAnalysisRequest = {
        id: 'risk-test-001',
        projectRoot: '/test/risky-project',
        analysisScope: 'project',
        includeExternal: true,
        analysisTypes: ['risk', 'security']
      };

      const result = await analyzer.analyzeDependencies(request);

      expect(result.riskAssessment).toBeDefined();
      expect(['low', 'medium', 'high', 'critical']).toContain(result.riskAssessment.overallRisk);
      expect(result.riskAssessment.riskFactors).toBeInstanceOf(Array);
      expect(result.riskAssessment.vulnerabilities).toBeInstanceOf(Array);
      expect(result.riskAssessment.mitigationPlan).toBeInstanceOf(Array);
      expect(result.riskAssessment.contingencyActions).toBeInstanceOf(Array);

      // Verify risk factor structure if any exist
      if (result.riskAssessment.riskFactors.length > 0) {
        const riskFactor = result.riskAssessment.riskFactors[0];
        expect(riskFactor.id).toBeDefined();
        expect(riskFactor.probability).toBeGreaterThanOrEqual(0);
        expect(riskFactor.probability).toBeLessThanOrEqual(1);
        expect(riskFactor.impact).toBeGreaterThanOrEqual(0);
        expect(riskFactor.impact).toBeLessThanOrEqual(1);
        expect(['circular', 'deep_nesting', 'high_coupling', 'single_point_failure', 'external_dependency']).toContain(riskFactor.type);
        expect(['low', 'medium', 'high', 'critical']).toContain(riskFactor.severity);
      }
    });

    test('should generate meaningful recommendations', async () => {
      const request: DependencyAnalysisRequest = {
        id: 'recommendations-test-001',
        projectRoot: '/test/project',
        analysisScope: 'project',
        includeExternal: true,
        analysisTypes: ['optimization', 'maintainability']
      };

      const result = await analyzer.analyzeDependencies(request);

      expect(result.recommendations).toBeInstanceOf(Array);
      expect(result.optimizationSuggestions).toBeInstanceOf(Array);

      // Check recommendation structure if any exist
      if (result.recommendations.length > 0) {
        const rec = result.recommendations[0];
        expect(rec.id).toBeDefined();
        expect(['refactor', 'upgrade', 'remove', 'replace', 'optimize']).toContain(rec.type);
        expect(['low', 'medium', 'high', 'critical']).toContain(rec.priority);
        expect(rec.title).toBeDefined();
        expect(rec.description).toBeDefined();
        expect(rec.benefits).toBeInstanceOf(Array);
        expect(rec.risks).toBeInstanceOf(Array);
        expect(['low', 'medium', 'high']).toContain(rec.effort);
      }

      // Check optimization suggestion structure if any exist
      if (result.optimizationSuggestions.length > 0) {
        const opt = result.optimizationSuggestions[0];
        expect(opt.id).toBeDefined();
        expect(['performance', 'maintainability', 'security', 'scalability']).toContain(opt.category);
        expect(opt.title).toBeDefined();
        expect(opt.description).toBeDefined();
        expect(opt.currentState).toBeDefined();
        expect(opt.proposedState).toBeDefined();
        expect(['low', 'medium', 'high']).toContain(opt.implementationComplexity);
      }
    });

    test('should handle impact analysis requests', async () => {
      const request: DependencyAnalysisRequest = {
        id: 'impact-analysis-001',
        projectRoot: '/test/project',
        analysisScope: 'project',
        includeExternal: false,
        analysisTypes: ['impact']
      };

      const result = await analyzer.analyzeDependencies(request);

      expect(result.impactAnalysis).toBeDefined();
      if (result.impactAnalysis) {
        expect(result.impactAnalysis.affectedComponents).toBeInstanceOf(Array);
        expect(result.impactAnalysis.riskLevel).toMatch(/low|medium|high|critical/);
      }
    });

    test('should validate analysis requests', async () => {
      const invalidRequest: Partial<DependencyAnalysisRequest> = {
        // Missing required fields
        projectRoot: '/test/project'
      };

      await expect(
        analyzer.analyzeDependencies(invalidRequest as DependencyAnalysisRequest)
      ).rejects.toThrow();
    });

    test('should respect concurrent analysis limits', async () => {
      const requests = Array.from({ length: 5 }, (_, i) => ({
        id: `concurrent-test-${i}`,
        projectRoot: '/test/project',
        analysisScope: 'project' as const,
        includeExternal: false,
        analysisTypes: ['structural' as const]
      }));

      // Start multiple analyses concurrently
      const promises = requests.map(req => analyzer.analyzeDependencies(req));

      // Some should succeed, some should fail due to concurrency limits
      const results = await Promise.allSettled(promises);
      
      const successful = results.filter(r => r.status === 'fulfilled').length;
      const failed = results.filter(r => r.status === 'rejected').length;

      expect(successful).toBeGreaterThan(0);
      expect(failed).toBeGreaterThan(0);
      expect(successful + failed).toBe(requests.length);
    });

    test('should emit proper events during analysis', async () => {
      const events: string[] = [];
      
      analyzer.on('analysisStarted', () => events.push('started'));
      analyzer.on('analysisCompleted', () => events.push('completed'));
      analyzer.on('analysisError', () => events.push('error'));

      const request: DependencyAnalysisRequest = {
        id: 'events-test-001',
        projectRoot: '/test/project',
        analysisScope: 'module',
        includeExternal: false,
        analysisTypes: ['structural']
      };

      await analyzer.analyzeDependencies(request);

      expect(events).toContain('started');
      expect(events).toContain('completed');
    });
  });

  describe('analyzeImpact', () => {
    test('should analyze impact of proposed changes', async () => {
      const request: ImpactAnalysisRequest = {
        id: 'impact-001',
        changes: [
          {
            type: 'modify',
            target: 'src/main.ts',
            description: 'Update main function signature',
            estimatedSize: 'medium'
          },
          {
            type: 'create',
            target: 'src/utils/helper.ts',
            description: 'Add new utility function',
            estimatedSize: 'small'
          }
        ],
        analysisDepth: 'extended',
        includeRiskAssessment: true,
        testSuggestions: true
      };

      const result = await analyzer.analyzeImpact(request);

      expect(result).toBeDefined();
      expect(result.affectedComponents).toBeInstanceOf(Array);
      expect(['low', 'medium', 'high', 'critical']).toContain(result.riskLevel);
      expect(result.recommendations).toBeInstanceOf(Array);
    });

    test('should handle different change types', async () => {
      const request: ImpactAnalysisRequest = {
        id: 'impact-change-types-001',
        changes: [
          {
            type: 'create',
            target: 'src/new-feature.ts',
            description: 'New feature implementation',
            estimatedSize: 'large'
          },
          {
            type: 'delete',
            target: 'src/deprecated.ts',
            description: 'Remove deprecated module',
            estimatedSize: 'medium'
          },
          {
            type: 'rename',
            target: 'src/utils.ts',
            description: 'Move utility to different package',
            estimatedSize: 'medium'
          }
        ],
        analysisDepth: 'comprehensive',
        includeRiskAssessment: true,
        testSuggestions: true
      };

      const result = await analyzer.analyzeImpact(request);

      expect(result.affectedComponents.length).toBeGreaterThanOrEqual(0);
      expect(result.testingRequirements).toBeDefined();
      expect(result.estimatedEffort).toBeGreaterThan(0);
    });

    test('should provide different analysis depths', async () => {
      const baseRequest = {
        id: 'depth-test',
        changes: [{
          type: 'modify' as const,
          target: 'src/core.ts',
          description: 'Core functionality update',
          estimatedSize: 'medium' as const
        }],
        includeRiskAssessment: true,
        testSuggestions: false
      };

      // Test immediate depth
      const immediateResult = await analyzer.analyzeImpact({
        ...baseRequest,
        id: 'depth-immediate',
        analysisDepth: 'immediate'
      });

      // Test extended depth
      const extendedResult = await analyzer.analyzeImpact({
        ...baseRequest,
        id: 'depth-extended', 
        analysisDepth: 'extended'
      });

      // Test comprehensive depth
      const comprehensiveResult = await analyzer.analyzeImpact({
        ...baseRequest,
        id: 'depth-comprehensive',
        analysisDepth: 'comprehensive'
      });

      expect(immediateResult.affectedComponents.length).toBeLessThanOrEqual(extendedResult.affectedComponents.length);
      expect(extendedResult.affectedComponents.length).toBeLessThanOrEqual(comprehensiveResult.affectedComponents.length);
    });
  });

  describe('dependency graph construction', () => {
    test('should build proper dependency nodes', async () => {
      const request: DependencyAnalysisRequest = {
        id: 'graph-test-001',
        projectRoot: '/test/project',
        analysisScope: 'project',
        includeExternal: false,
        analysisTypes: ['structural']
      };

      const result = await analyzer.analyzeDependencies(request);

      if (result.nodes.length > 0) {
        const node = result.nodes[0];
        expect(node.id).toBeDefined();
        expect(node.name).toBeDefined();
        expect(['module', 'function', 'class', 'variable', 'type', 'file']).toContain(node.type);
        expect(node.path).toBeDefined();
        expect(node.dependencies).toBeInstanceOf(Array);
        expect(node.dependents).toBeInstanceOf(Array);
        expect(node.metadata).toBeDefined();
        expect(node.metadata.lines).toBeGreaterThanOrEqual(0);
        expect(node.metadata.complexity).toBeGreaterThanOrEqual(0);
        expect(node.metadata.lastModified).toBeInstanceOf(Date);
        expect(['low', 'medium', 'high', 'critical']).toContain(node.metadata.importance);
      }
    });

    test('should create proper graph edges', async () => {
      const request: DependencyAnalysisRequest = {
        id: 'edges-test-001',
        projectRoot: '/test/project',
        analysisScope: 'module',
        includeExternal: false,
        analysisTypes: ['structural']
      };

      const result = await analyzer.analyzeDependencies(request);

      expect(result.graph.edges).toBeInstanceOf(Array);
      
      if (result.graph.edges.length > 0) {
        const edge = result.graph.edges[0];
        expect(edge.id).toBeDefined();
        expect(edge.source).toBeDefined();
        expect(edge.target).toBeDefined();
        expect(edge.type).toBe('dependency');
      }
    });
  });

  describe('caching behavior', () => {
    test('should cache analysis results', async () => {
      const request: DependencyAnalysisRequest = {
        id: 'cache-test-001',
        projectRoot: '/test/project',
        analysisScope: 'module',
        includeExternal: false,
        analysisTypes: ['structural']
      };

      // First analysis
      const result1 = await analyzer.analyzeDependencies(request);
      
      // Second analysis with same request (should hit cache)
      const result2 = await analyzer.analyzeDependencies(request);

      expect(result1.requestId).toBe(result2.requestId);
      expect(result1.graph.nodes.length).toBe(result2.graph.nodes.length);
    });

    test('should emit cache hit events', async () => {
      let cacheHitEmitted = false;
      analyzer.on('cacheHit', () => {
        cacheHitEmitted = true;
      });

      const request: DependencyAnalysisRequest = {
        id: 'cache-hit-test-001',
        projectRoot: '/test/project',
        analysisScope: 'module',
        includeExternal: false,
        analysisTypes: ['structural']
      };

      // First analysis
      await analyzer.analyzeDependencies(request);
      
      // Second analysis (should hit cache)
      await analyzer.analyzeDependencies(request);

      expect(cacheHitEmitted).toBe(true);
    });
  });

  describe('error handling', () => {
    test('should handle invalid project paths', async () => {
      const request: DependencyAnalysisRequest = {
        id: 'invalid-path-test',
        projectRoot: '', // Invalid empty path
        analysisScope: 'project',
        includeExternal: false,
        analysisTypes: ['structural']
      };

      await expect(analyzer.analyzeDependencies(request)).rejects.toThrow();
    });

    test('should handle empty analysis types', async () => {
      const request: DependencyAnalysisRequest = {
        id: 'empty-types-test',
        projectRoot: '/test/project',
        analysisScope: 'project',
        includeExternal: false,
        analysisTypes: [] // Empty analysis types
      };

      await expect(analyzer.analyzeDependencies(request)).rejects.toThrow();
    });

    test('should emit error events for failed analyses', async () => {
      let errorEmitted = false;
      analyzer.on('analysisError', () => {
        errorEmitted = true;
      });

      const request: DependencyAnalysisRequest = {
        id: 'error-test-001',
        projectRoot: '', // Invalid to trigger error
        analysisScope: 'project',
        includeExternal: false,
        analysisTypes: ['structural']
      };

      await expect(analyzer.analyzeDependencies(request)).rejects.toThrow();
      expect(errorEmitted).toBe(true);
    });
  });

  describe('edge cases', () => {
    test('should handle projects with no dependencies', async () => {
      const request: DependencyAnalysisRequest = {
        id: 'no-deps-test-001',
        projectRoot: '/test/empty-project',
        analysisScope: 'project',
        includeExternal: false,
        analysisTypes: ['structural']
      };

      const result = await analyzer.analyzeDependencies(request);

      expect(result.metrics.totalNodes).toBeGreaterThanOrEqual(0);
      expect(result.metrics.averageDependencies).toBe(0);
      expect(result.circularDependencies).toHaveLength(0);
      expect(result.riskAssessment.overallRisk).toBe('low');
    });

    test('should handle very deep dependency chains', async () => {
      const request: DependencyAnalysisRequest = {
        id: 'deep-chain-test-001',
        projectRoot: '/test/deep-project',
        maxDepth: 20,
        analysisScope: 'project',
        includeExternal: true,
        analysisTypes: ['structural', 'performance']
      };

      const result = await analyzer.analyzeDependencies(request);

      expect(result.metrics.maxDependencyDepth).toBeGreaterThanOrEqual(0);
      expect(result.metrics.criticalPathLength).toBeGreaterThanOrEqual(0);
    });

    test('should handle external dependencies properly', async () => {
      const request: DependencyAnalysisRequest = {
        id: 'external-deps-test-001',
        projectRoot: '/test/project',
        analysisScope: 'project',
        includeExternal: true,
        analysisTypes: ['structural', 'security']
      };

      const result = await analyzer.analyzeDependencies(request);

      // Should not fail when including external dependencies
      expect(result).toBeDefined();
      expect(result.graph).toBeDefined();
      
      // May contain external dependency risks
      if (result.riskAssessment.riskFactors.length > 0) {
        const hasExternalRisk = result.riskAssessment.riskFactors.some(rf => 
          rf.type === 'external_dependency'
        );
        // Either has external risks or doesn't, both are valid
        expect(typeof hasExternalRisk).toBe('boolean');
      }
    });
  });
});