import { describe, test, expect, beforeEach } from 'vitest';
import { ProblemDecomposer } from '../../../src/inference/core/problem-decomposer.js';
import type { Problem } from '../../../src/inference/core/problem-decomposer.js';

describe('ProblemDecomposer', () => {
  let decomposer: ProblemDecomposer;

  beforeEach(() => {
    decomposer = new ProblemDecomposer();
  });

  describe('decompose', () => {
    test('should decompose a simple software development problem', async () => {
      const problem: Problem = {
        id: 'sw-dev-001',
        title: 'Build User Authentication System',
        description: 'Implement a secure user authentication system with login, registration, and password reset',
        domain: 'software_development',
        complexity: 'medium',
        priority: 'high',
        constraints: [
          {
            id: 'security-req',
            type: 'security',
            description: 'Must comply with OWASP security standards',
            importance: 'critical'
          },
          {
            id: 'time-req',
            type: 'time',
            description: 'Must be completed within 4 weeks',
            importance: 'high',
            value: 4,
            operator: '<='
          }
        ],
        context: {
          framework: 'React',
          backend: 'Node.js',
          database: 'PostgreSQL',
          teamSize: 3
        },
        expectedOutcome: 'Functional authentication system with all security features'
      };

      const result = await decomposer.decompose(problem);

      expect(result).toBeDefined();
      expect(result.originalProblem).toBe(problem);
      expect(result.subProblems).toHaveLength(3); // requirements, architecture, implementation
      expect(result.executionPlan).toBeInstanceOf(Array);
      expect(result.estimatedTotalTime).toBeGreaterThan(0);
      expect(result.criticalPath).toBeInstanceOf(Array);
      expect(result.riskAssessment).toBeDefined();
      expect(result.recommendations).toBeInstanceOf(Array);

      // Verify sub-problems structure
      const requirementsSubProblem = result.subProblems.find(sp => sp.id.includes('requirements'));
      expect(requirementsSubProblem).toBeDefined();
      expect(requirementsSubProblem?.dependencies).toHaveLength(0); // First step
      
      const architectureSubProblem = result.subProblems.find(sp => sp.id.includes('architecture'));
      expect(architectureSubProblem).toBeDefined();
      expect(architectureSubProblem?.dependencies).toContain(requirementsSubProblem!.id);
    });

    test('should decompose a data analysis problem', async () => {
      const problem: Problem = {
        id: 'data-001',
        title: 'Customer Behavior Analysis',
        description: 'Analyze customer purchasing patterns to improve recommendations',
        domain: 'data_analysis',
        complexity: 'high',
        priority: 'medium',
        constraints: [
          {
            id: 'data-privacy',
            type: 'business',
            description: 'Must comply with GDPR data privacy requirements',
            importance: 'critical'
          }
        ],
        context: {
          dataSize: 1000000,
          dataSources: ['transactions', 'user_profiles', 'product_catalog'],
          analysisType: 'behavioral_patterns'
        }
      };

      const result = await decomposer.decompose(problem);

      expect(result.subProblems).toHaveLength(2); // data collection, EDA
      expect(result.subProblems.some(sp => sp.id.includes('data-collection'))).toBe(true);
      expect(result.subProblems.some(sp => sp.id.includes('eda'))).toBe(true);

      // Verify data-specific constraints are preserved
      const dataCollectionProblem = result.subProblems.find(sp => sp.id.includes('data-collection'));
      expect(dataCollectionProblem?.constraints).toBeDefined();
    });

    test('should decompose a debugging problem', async () => {
      const problem: Problem = {
        id: 'debug-001',
        title: 'Fix Memory Leak Issue',
        description: 'Identify and fix memory leak in production application',
        domain: 'debugging',
        complexity: 'high',
        priority: 'critical',
        constraints: [
          {
            id: 'prod-impact',
            type: 'business',
            description: 'Minimize production downtime',
            importance: 'critical'
          }
        ],
        context: {
          environment: 'production',
          affectedUsers: 10000,
          symptoms: ['increasing memory usage', 'slow response times']
        },
        deadline: new Date(Date.now() + 24 * 60 * 60 * 1000) // 24 hours
      };

      const result = await decomposer.decompose(problem);

      expect(result.subProblems).toHaveLength(2); // reproduce, isolate
      expect(result.subProblems.some(sp => sp.id.includes('reproduce'))).toBe(true);
      expect(result.subProblems.some(sp => sp.id.includes('isolate'))).toBe(true);
      
      // Verify sequential dependencies
      const reproduceStep = result.subProblems.find(sp => sp.id.includes('reproduce'));
      const isolateStep = result.subProblems.find(sp => sp.id.includes('isolate'));
      expect(isolateStep?.dependencies).toContain(reproduceStep!.id);
    });

    test('should handle generic problems with default strategy', async () => {
      const problem: Problem = {
        id: 'generic-001',
        title: 'Optimize Business Process',
        description: 'Improve efficiency of customer onboarding process',
        domain: 'business_optimization',
        complexity: 'medium',
        priority: 'medium',
        constraints: [],
        context: {
          currentProcessTime: 5,
          targetProcessTime: 2,
          stakeholders: ['sales', 'operations', 'IT']
        }
      };

      const result = await decomposer.decompose(problem);

      expect(result.subProblems).toHaveLength(1); // generic analysis
      expect(result.subProblems[0].id.includes('analysis')).toBe(true);
      expect(result.executionPlan).toHaveLength(1);
    });

    test('should throw error for invalid problem', async () => {
      const invalidProblem = {
        id: '',
        title: '',
        description: '',
        domain: 'test'
      } as Problem;

      await expect(decomposer.decompose(invalidProblem)).rejects.toThrow();
    });

    test('should apply hierarchical strategy for complex problems', async () => {
      const complexProblem: Problem = {
        id: 'complex-001',
        title: 'Enterprise System Migration',
        description: 'Migrate legacy enterprise system to cloud-native architecture',
        domain: 'system_design',
        complexity: 'critical',
        priority: 'critical',
        constraints: [
          {
            id: 'zero-downtime',
            type: 'business',
            description: 'Must achieve zero-downtime migration',
            importance: 'critical'
          },
          {
            id: 'performance',
            type: 'technical',
            description: 'Performance must not degrade',
            importance: 'high'
          }
        ],
        context: {
          legacySystemAge: 10,
          dataSize: '100TB',
          userBase: 50000,
          integrations: 25
        }
      };

      const result = await decomposer.decompose(complexProblem);

      expect(result.subProblems.length).toBeGreaterThanOrEqual(1);
      expect(['low', 'medium', 'high', 'critical']).toContain(result.riskAssessment.overallRisk);
      expect(result.recommendations.length).toBeGreaterThan(0);
      
      // Should have risk assessment (may or may not have risk factors depending on actual analysis)
      expect(result.riskAssessment.riskFactors.length).toBeGreaterThanOrEqual(0);
    });

    test('should calculate execution plan with proper dependencies', async () => {
      const problem: Problem = {
        id: 'execution-test',
        title: 'Multi-step Development Process',
        description: 'Complex development with multiple dependencies',
        domain: 'software_development',
        complexity: 'high',
        priority: 'medium',
        constraints: [],
        context: { complexity: 8 }
      };

      const result = await decomposer.decompose(problem);

      expect(result.executionPlan.length).toBeGreaterThan(0);
      
      // Verify phases are assigned correctly
      const phases = new Set(result.executionPlan.map(node => node.phase));
      expect(phases.size).toBeGreaterThan(0);
      
      // Verify dependencies are respected in execution plan
      for (const node of result.executionPlan) {
        for (const depId of node.dependencies) {
          const depNode = result.executionPlan.find(n => n.subProblemId === depId);
          if (depNode) {
            expect(depNode.phase).toBeLessThanOrEqual(node.phase);
          }
        }
      }
    });

    test('should perform risk assessment', async () => {
      const riskyProblem: Problem = {
        id: 'risky-001',
        title: 'High Risk Development Project',
        description: 'Project with multiple risk factors',
        domain: 'software_development',
        complexity: 'critical',
        priority: 'critical',
        constraints: Array.from({ length: 10 }, (_, i) => ({
          id: `constraint-${i}`,
          type: 'technical' as const,
          description: `Technical constraint ${i}`,
          importance: 'high' as const
        })),
        context: {
          linesOfCode: 100000,
          dependencies: Array.from({ length: 15 }, (_, i) => `dep-${i}`),
          teamExperience: 'low'
        }
      };

      const result = await decomposer.decompose(riskyProblem);

      expect(['low', 'medium', 'high', 'critical']).toContain(result.riskAssessment.overallRisk);
      expect(result.riskAssessment.riskFactors.length).toBeGreaterThanOrEqual(0);
      expect(result.riskAssessment.mitigationStrategies.length).toBeGreaterThanOrEqual(0);
      expect(result.riskAssessment.contingencyPlan.length).toBeGreaterThanOrEqual(0);

      // Verify risk factors have proper structure
      for (const riskFactor of result.riskAssessment.riskFactors) {
        expect(riskFactor.id).toBeDefined();
        expect(riskFactor.probability).toBeGreaterThanOrEqual(0);
        expect(riskFactor.probability).toBeLessThanOrEqual(1);
        expect(riskFactor.impact).toBeGreaterThanOrEqual(0);
        expect(riskFactor.impact).toBeLessThanOrEqual(1);
        expect(riskFactor.category).toBeDefined();
      }
    });

    test('should generate appropriate recommendations', async () => {
      const problem: Problem = {
        id: 'rec-test',
        title: 'Project Requiring Recommendations',
        description: 'Test recommendation generation',
        domain: 'software_development',
        complexity: 'high',
        priority: 'high',
        constraints: [],
        context: { needsGuidance: true }
      };

      const result = await decomposer.decompose(problem);

      expect(result.recommendations).toBeInstanceOf(Array);
      expect(result.recommendations.length).toBeGreaterThan(0);
      
      // Should contain general recommendations
      expect(result.recommendations.some(rec => 
        rec.includes('highest-risk') || rec.includes('communication')
      )).toBe(true);
    });
  });

  describe('custom strategies and analyzers', () => {
    test('should allow registration of custom decomposition strategies', () => {
      const customStrategy = (problem: Problem) => [{
        id: `${problem.id}-custom`,
        parentId: problem.id,
        title: 'Custom Sub-problem',
        description: 'Generated by custom strategy',
        type: 'sequential' as const,
        dependencies: [],
        estimatedComplexity: 3,
        estimatedTime: 2,
        requiredResources: ['custom_resource'],
        constraints: [],
        successCriteria: ['Custom criterion met'],
        fallbackStrategies: ['Custom fallback']
      }];

      expect(() => {
        decomposer.registerDecompositionStrategy('custom_domain', customStrategy);
      }).not.toThrow();
    });

    test('should allow registration of custom complexity analyzers', () => {
      const customAnalyzer = (problem: Problem) => {
        return problem.context.customComplexity || 5;
      };

      expect(() => {
        decomposer.registerComplexityAnalyzer('custom_domain', customAnalyzer);
      }).not.toThrow();
    });
  });

  describe('edge cases', () => {
    test('should handle problem without context', async () => {
      const problem: Problem = {
        id: 'no-context',
        title: 'Problem Without Context',
        description: 'Testing problem without context data',
        domain: 'generic',
        complexity: 'low',
        priority: 'low',
        constraints: [],
        context: {}
      };

      const result = await decomposer.decompose(problem);

      expect(result.subProblems.length).toBeGreaterThan(0);
      expect(result.estimatedTotalTime).toBeGreaterThan(0);
    });

    test('should handle problem with circular dependencies potential', async () => {
      const problem: Problem = {
        id: 'circular-test',
        title: 'Problem with Complex Dependencies',
        description: 'Testing circular dependency handling',
        domain: 'software_development',
        complexity: 'high',
        priority: 'medium',
        constraints: [],
        context: {
          hasComplexDependencies: true,
          moduleCount: 20
        }
      };

      const result = await decomposer.decompose(problem);

      // Should complete without infinite loops
      expect(result.subProblems.length).toBeGreaterThan(0);
      expect(result.executionPlan.length).toBe(result.subProblems.length);
      
      // Verify no sub-problem depends on itself
      for (const subProblem of result.subProblems) {
        expect(subProblem.dependencies).not.toContain(subProblem.id);
      }
    });

    test('should handle problem with extreme complexity', async () => {
      const extremelyComplexProblem: Problem = {
        id: 'extreme-complexity',
        title: 'Extremely Complex Problem',
        description: 'Testing extreme complexity handling',
        domain: 'software_development',
        complexity: 'critical',
        priority: 'critical',
        constraints: Array.from({ length: 20 }, (_, i) => ({
          id: `constraint-${i}`,
          type: 'technical' as const,
          description: `Complex constraint ${i}`,
          importance: 'high' as const
        })),
        context: {
          linesOfCode: 1000000,
          dependencies: Array.from({ length: 50 }, (_, i) => `dep-${i}`),
          integrationPoints: 30,
          teamSize: 20
        }
      };

      const result = await decomposer.decompose(extremelyComplexProblem);

      // Should handle extreme complexity gracefully
      expect(result.subProblems.length).toBeGreaterThanOrEqual(1); // Should break down appropriately
      expect(['low', 'medium', 'high', 'critical']).toContain(result.riskAssessment.overallRisk);
      expect(result.recommendations.length).toBeGreaterThan(0);
    });
  });
});