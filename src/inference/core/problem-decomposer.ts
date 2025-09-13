/**
 * Problem Decomposer for Complex Problem Solving Framework
 * Breaks down complex problems into manageable sub-problems
 */

export interface Problem {
  id: string;
  title: string;
  description: string;
  domain: string;
  complexity: 'low' | 'medium' | 'high' | 'critical';
  priority: 'low' | 'medium' | 'high' | 'critical';
  constraints: Constraint[];
  context: Record<string, any>;
  expectedOutcome?: string;
  deadline?: Date;
}

export interface Constraint {
  id: string;
  type: 'resource' | 'time' | 'quality' | 'dependency' | 'business' | 'technical';
  description: string;
  importance: 'low' | 'medium' | 'high' | 'critical';
  value?: any;
  operator?: '>' | '<' | '>=' | '<=' | '=' | '!=' | 'in' | 'not_in';
}

export interface SubProblem {
  id: string;
  parentId: string;
  title: string;
  description: string;
  type: 'sequential' | 'parallel' | 'conditional' | 'loop';
  dependencies: string[];
  estimatedComplexity: number;
  estimatedTime: number;
  requiredResources: string[];
  constraints: Constraint[];
  successCriteria: string[];
  fallbackStrategies: string[];
}

export interface DecompositionResult {
  originalProblem: Problem;
  subProblems: SubProblem[];
  executionPlan: ExecutionNode[];
  estimatedTotalTime: number;
  criticalPath: string[];
  riskAssessment: RiskAssessment;
  recommendations: string[];
}

export interface ExecutionNode {
  id: string;
  subProblemId: string;
  phase: number;
  canRunInParallel: boolean;
  dependencies: string[];
  estimatedStartTime: number;
  estimatedEndTime: number;
}

export interface RiskAssessment {
  overallRisk: 'low' | 'medium' | 'high' | 'critical';
  riskFactors: RiskFactor[];
  mitigationStrategies: MitigationStrategy[];
  contingencyPlan: string[];
}

export interface RiskFactor {
  id: string;
  description: string;
  probability: number; // 0-1
  impact: number; // 0-1
  category: 'technical' | 'resource' | 'time' | 'quality' | 'external';
  mitigation?: string;
}

export interface MitigationStrategy {
  riskId: string;
  strategy: string;
  cost: number;
  effectiveness: number; // 0-1
  timeRequired: number;
}

export class ProblemDecomposer {
  private decompositionStrategies = new Map<string, (problem: Problem) => SubProblem[]>();
  private complexityAnalyzers = new Map<string, (problem: Problem) => number>();

  constructor() {
    this.registerDefaultStrategies();
    this.registerDefaultAnalyzers();
  }

  /**
   * Decompose a complex problem into manageable sub-problems
   */
  async decompose(problem: Problem): Promise<DecompositionResult> {
    // Validate problem
    this.validateProblem(problem);

    // Analyze complexity and select strategy
    const complexity = this.analyzeComplexity(problem);
    const strategy = this.selectDecompositionStrategy(problem, complexity);

    // Generate sub-problems
    const subProblems = await this.generateSubProblems(problem, strategy);

    // Create execution plan
    const executionPlan = this.createExecutionPlan(subProblems);

    // Calculate estimates
    const estimatedTotalTime = this.calculateTotalTime(executionPlan);
    const criticalPath = this.findCriticalPath(executionPlan);

    // Perform risk assessment
    const riskAssessment = this.performRiskAssessment(problem, subProblems);

    // Generate recommendations
    const recommendations = this.generateRecommendations(problem, subProblems, riskAssessment);

    return {
      originalProblem: problem,
      subProblems,
      executionPlan,
      estimatedTotalTime,
      criticalPath,
      riskAssessment,
      recommendations
    };
  }

  /**
   * Register a custom decomposition strategy
   */
  registerDecompositionStrategy(domain: string, strategy: (problem: Problem) => SubProblem[]): void {
    this.decompositionStrategies.set(domain, strategy);
  }

  /**
   * Register a custom complexity analyzer
   */
  registerComplexityAnalyzer(domain: string, analyzer: (problem: Problem) => number): void {
    this.complexityAnalyzers.set(domain, analyzer);
  }

  private registerDefaultStrategies(): void {
    this.decompositionStrategies.set('software_development', this.decomposeSoftwareProblem.bind(this));
    this.decompositionStrategies.set('data_analysis', this.decomposeDataProblem.bind(this));
    this.decompositionStrategies.set('system_design', this.decomposeSystemProblem.bind(this));
    this.decompositionStrategies.set('debugging', this.decomposeDebuggingProblem.bind(this));
    this.decompositionStrategies.set('optimization', this.decomposeOptimizationProblem.bind(this));
    this.decompositionStrategies.set('default', this.decomposeGenericProblem.bind(this));
  }

  private registerDefaultAnalyzers(): void {
    this.complexityAnalyzers.set('software_development', this.analyzeSoftwareComplexity.bind(this));
    this.complexityAnalyzers.set('data_analysis', this.analyzeDataComplexity.bind(this));
    this.complexityAnalyzers.set('default', this.analyzeGenericComplexity.bind(this));
  }

  private validateProblem(problem: Problem): void {
    if (!problem.id || !problem.title || !problem.description) {
      throw new Error('Problem must have id, title, and description');
    }

    if (!problem.domain) {
      throw new Error('Problem domain is required');
    }
  }

  private analyzeComplexity(problem: Problem): number {
    const analyzer = this.complexityAnalyzers.get(problem.domain) || 
                    this.complexityAnalyzers.get('default')!;
    return analyzer(problem);
  }

  private selectDecompositionStrategy(problem: Problem, complexity: number): string {
    if (complexity > 8) {
      return 'hierarchical';
    } else if (complexity > 5) {
      return 'modular';
    } else {
      return 'sequential';
    }
  }

  private async generateSubProblems(problem: Problem, strategy: string): Promise<SubProblem[]> {
    const decomposer = this.decompositionStrategies.get(problem.domain) || 
                      this.decompositionStrategies.get('default')!;
    
    let subProblems = decomposer(problem);
    
    // Apply strategy-specific modifications
    subProblems = this.applyDecompositionStrategy(subProblems, strategy);
    
    // Optimize sub-problem organization
    subProblems = this.optimizeSubProblems(subProblems);
    
    return subProblems;
  }

  private decomposeSoftwareProblem(problem: Problem): SubProblem[] {
    const subProblems: SubProblem[] = [];
    
    // Requirements analysis
    subProblems.push({
      id: `${problem.id}-requirements`,
      parentId: problem.id,
      title: 'Requirements Analysis',
      description: 'Analyze and define detailed requirements',
      type: 'sequential',
      dependencies: [],
      estimatedComplexity: 3,
      estimatedTime: 2,
      requiredResources: ['analyst', 'documentation'],
      constraints: problem.constraints.filter(c => c.type === 'business' || c.type === 'quality'),
      successCriteria: ['Requirements documented', 'Stakeholder approval'],
      fallbackStrategies: ['Incremental requirements gathering', 'Prototype-based validation']
    });

    // Architecture design
    subProblems.push({
      id: `${problem.id}-architecture`,
      parentId: problem.id,
      title: 'System Architecture Design',
      description: 'Design system architecture and component structure',
      type: 'sequential',
      dependencies: [`${problem.id}-requirements`],
      estimatedComplexity: 5,
      estimatedTime: 4,
      requiredResources: ['architect', 'design_tools'],
      constraints: problem.constraints.filter(c => c.type === 'technical' || c.type === 'resource'),
      successCriteria: ['Architecture documented', 'Technical review passed'],
      fallbackStrategies: ['Iterative design', 'Proof of concept']
    });

    // Implementation planning
    subProblems.push({
      id: `${problem.id}-implementation`,
      parentId: problem.id,
      title: 'Implementation Planning',
      description: 'Plan development phases and resource allocation',
      type: 'parallel',
      dependencies: [`${problem.id}-architecture`],
      estimatedComplexity: 4,
      estimatedTime: 3,
      requiredResources: ['project_manager', 'development_team'],
      constraints: problem.constraints.filter(c => c.type === 'time' || c.type === 'resource'),
      successCriteria: ['Development plan approved', 'Team assigned'],
      fallbackStrategies: ['Agile methodology', 'MVP approach']
    });

    return subProblems;
  }

  private decomposeDataProblem(problem: Problem): SubProblem[] {
    const subProblems: SubProblem[] = [];
    
    // Data collection
    subProblems.push({
      id: `${problem.id}-data-collection`,
      parentId: problem.id,
      title: 'Data Collection and Preparation',
      description: 'Gather and prepare data for analysis',
      type: 'sequential',
      dependencies: [],
      estimatedComplexity: 3,
      estimatedTime: 2,
      requiredResources: ['data_engineer', 'data_sources'],
      constraints: problem.constraints.filter(c => c.type === 'resource' || c.type === 'quality'),
      successCriteria: ['Data collected', 'Quality validated'],
      fallbackStrategies: ['Synthetic data', 'Sample dataset']
    });

    // Exploratory analysis
    subProblems.push({
      id: `${problem.id}-eda`,
      parentId: problem.id,
      title: 'Exploratory Data Analysis',
      description: 'Perform initial data exploration and pattern identification',
      type: 'parallel',
      dependencies: [`${problem.id}-data-collection`],
      estimatedComplexity: 4,
      estimatedTime: 3,
      requiredResources: ['data_scientist', 'analysis_tools'],
      constraints: [],
      successCriteria: ['Patterns identified', 'Insights documented'],
      fallbackStrategies: ['Automated EDA', 'Statistical summaries']
    });

    return subProblems;
  }

  private decomposeSystemProblem(problem: Problem): SubProblem[] {
    return [
      {
        id: `${problem.id}-system-analysis`,
        parentId: problem.id,
        title: 'System Analysis',
        description: 'Analyze current system state and requirements',
        type: 'sequential',
        dependencies: [],
        estimatedComplexity: 4,
        estimatedTime: 3,
        requiredResources: ['system_analyst'],
        constraints: problem.constraints,
        successCriteria: ['System understood', 'Requirements clear'],
        fallbackStrategies: ['Incremental analysis', 'Proof of concept']
      }
    ];
  }

  private decomposeDebuggingProblem(problem: Problem): SubProblem[] {
    return [
      {
        id: `${problem.id}-reproduce`,
        parentId: problem.id,
        title: 'Issue Reproduction',
        description: 'Reproduce the issue consistently',
        type: 'sequential',
        dependencies: [],
        estimatedComplexity: 2,
        estimatedTime: 1,
        requiredResources: ['developer', 'test_environment'],
        constraints: problem.constraints,
        successCriteria: ['Issue reproduced', 'Steps documented'],
        fallbackStrategies: ['Log analysis', 'User report analysis']
      },
      {
        id: `${problem.id}-isolate`,
        parentId: problem.id,
        title: 'Issue Isolation',
        description: 'Isolate the root cause of the issue',
        type: 'sequential',
        dependencies: [`${problem.id}-reproduce`],
        estimatedComplexity: 5,
        estimatedTime: 4,
        requiredResources: ['developer', 'debugging_tools'],
        constraints: [],
        successCriteria: ['Root cause identified', 'Fix strategy planned'],
        fallbackStrategies: ['Binary search', 'Code review']
      }
    ];
  }

  private decomposeOptimizationProblem(problem: Problem): SubProblem[] {
    return [
      {
        id: `${problem.id}-baseline`,
        parentId: problem.id,
        title: 'Baseline Measurement',
        description: 'Establish current performance baseline',
        type: 'sequential',
        dependencies: [],
        estimatedComplexity: 2,
        estimatedTime: 1,
        requiredResources: ['performance_engineer', 'monitoring_tools'],
        constraints: problem.constraints,
        successCriteria: ['Baseline established', 'Metrics defined'],
        fallbackStrategies: ['Synthetic benchmarks', 'Historical data']
      }
    ];
  }

  private decomposeGenericProblem(problem: Problem): SubProblem[] {
    return [
      {
        id: `${problem.id}-analysis`,
        parentId: problem.id,
        title: 'Problem Analysis',
        description: 'Analyze the problem and identify key components',
        type: 'sequential',
        dependencies: [],
        estimatedComplexity: 3,
        estimatedTime: 2,
        requiredResources: ['analyst'],
        constraints: problem.constraints,
        successCriteria: ['Problem understood', 'Approach defined'],
        fallbackStrategies: ['Iterative analysis', 'Expert consultation']
      }
    ];
  }

  private analyzeSoftwareComplexity(problem: Problem): number {
    let complexity = 0;
    
    // Base complexity
    complexity += 3;
    
    // Add complexity based on context
    if (problem.context['linesOfCode']) {
      complexity += Math.min(3, (problem.context['linesOfCode'] as number) / 10000);
    }
    
    if (problem.context['dependencies']) {
      complexity += Math.min(2, (problem.context['dependencies'] as any[]).length / 10);
    }
    
    if (problem.constraints.length > 5) {
      complexity += 2;
    }
    
    return Math.min(10, complexity);
  }

  private analyzeDataComplexity(problem: Problem): number {
    let complexity = 0;
    
    complexity += 2; // Base complexity
    
    if (problem.context['dataSize']) {
      complexity += Math.min(3, Math.log10(problem.context['dataSize'] as number) / 2);
    }
    
    if (problem.context['dataSources']) {
      complexity += Math.min(2, (problem.context['dataSources'] as any[]).length / 5);
    }
    
    return Math.min(10, complexity);
  }

  private analyzeGenericComplexity(problem: Problem): number {
    let complexity = 0;
    
    // Base complexity by problem complexity level
    switch (problem.complexity) {
      case 'low': complexity = 2; break;
      case 'medium': complexity = 4; break;
      case 'high': complexity = 7; break;
      case 'critical': complexity = 9; break;
    }
    
    // Adjust for constraints
    complexity += Math.min(2, problem.constraints.length / 3);
    
    return Math.min(10, complexity);
  }

  private applyDecompositionStrategy(subProblems: SubProblem[], strategy: string): SubProblem[] {
    switch (strategy) {
      case 'hierarchical':
        return this.applyHierarchicalStrategy(subProblems);
      case 'modular':
        return this.applyModularStrategy(subProblems);
      case 'sequential':
        return this.applySequentialStrategy(subProblems);
      default:
        return subProblems;
    }
  }

  private applyHierarchicalStrategy(subProblems: SubProblem[]): SubProblem[] {
    // Create additional decomposition levels for complex sub-problems
    const complexSubProblems = subProblems.filter(sp => sp.estimatedComplexity > 6);
    const additionalSubProblems: SubProblem[] = [];
    
    for (const complex of complexSubProblems) {
      // Create sub-sub-problems
      additionalSubProblems.push({
        ...complex,
        id: `${complex.id}-phase1`,
        title: `${complex.title} - Phase 1`,
        estimatedComplexity: Math.ceil(complex.estimatedComplexity / 2),
        estimatedTime: Math.ceil(complex.estimatedTime / 2)
      });
      
      additionalSubProblems.push({
        ...complex,
        id: `${complex.id}-phase2`,
        title: `${complex.title} - Phase 2`,
        dependencies: [`${complex.id}-phase1`],
        estimatedComplexity: Math.floor(complex.estimatedComplexity / 2),
        estimatedTime: Math.floor(complex.estimatedTime / 2)
      });
    }
    
    // Replace complex sub-problems with phases
    const simpleSubProblems = subProblems.filter(sp => sp.estimatedComplexity <= 6);
    return [...simpleSubProblems, ...additionalSubProblems];
  }

  private applyModularStrategy(subProblems: SubProblem[]): SubProblem[] {
    // Group related sub-problems into modules
    return subProblems.map(sp => ({
      ...sp,
      type: 'parallel' as const // Enable parallel execution where possible
    }));
  }

  private applySequentialStrategy(subProblems: SubProblem[]): SubProblem[] {
    // Ensure sequential execution
    return subProblems.map((sp, index) => ({
      ...sp,
      type: 'sequential' as const,
      dependencies: index > 0 ? [subProblems[index - 1].id] : []
    }));
  }

  private optimizeSubProblems(subProblems: SubProblem[]): SubProblem[] {
    // Remove redundant dependencies
    const optimized = subProblems.map(sp => ({
      ...sp,
      dependencies: this.removeRedundantDependencies(sp.dependencies || [], subProblems)
    }));
    
    // Balance workload
    return this.balanceWorkload(optimized);
  }

  private removeRedundantDependencies(dependencies: string[], allSubProblems: SubProblem[]): string[] {
    const necessary = new Set<string>();
    
    for (const dep of dependencies) {
      const depSubProblem = allSubProblems.find(sp => sp.id === dep);
      if (depSubProblem) {
        // Check if this dependency is already covered by another dependency
        const isCovered = dependencies.some(otherDep => {
          if (otherDep === dep) return false;
          const otherDepSubProblem = allSubProblems.find(sp => sp.id === otherDep);
          return otherDepSubProblem?.dependencies?.includes(dep) ?? false;
        });
        
        if (!isCovered) {
          necessary.add(dep);
        }
      }
    }
    
    return Array.from(necessary);
  }

  private balanceWorkload(subProblems: SubProblem[]): SubProblem[] {
    // Simple load balancing - could be more sophisticated
    const avgComplexity = subProblems.reduce((sum, sp) => sum + sp.estimatedComplexity, 0) / subProblems.length;
    
    return subProblems.map(sp => {
      if (sp.estimatedComplexity > avgComplexity * 1.5) {
        // This sub-problem is significantly more complex, consider splitting
        return {
          ...sp,
          fallbackStrategies: [...sp.fallbackStrategies, 'Consider further decomposition']
        };
      }
      return sp;
    });
  }

  private createExecutionPlan(subProblems: SubProblem[]): ExecutionNode[] {
    const nodes: ExecutionNode[] = [];
    const processed = new Set<string>();
    const phases = new Map<number, string[]>();
    
    // Assign phases based on dependencies
    const assignPhase = (subProblem: SubProblem): number => {
      if (subProblem.dependencies.length === 0) {
        return 0;
      }
      
      let maxPhase = -1;
      for (const depId of subProblem.dependencies) {
        const depNode = nodes.find(n => n.subProblemId === depId);
        if (depNode) {
          maxPhase = Math.max(maxPhase, depNode.phase);
        }
      }
      
      return maxPhase + 1;
    };
    
    // Process sub-problems in dependency order
    while (processed.size < subProblems.length) {
      for (const subProblem of subProblems) {
        if (processed.has(subProblem.id)) continue;
        
        const allDepsSatisfied = subProblem.dependencies.every(depId => processed.has(depId));
        if (allDepsSatisfied) {
          const phase = assignPhase(subProblem);
          const node: ExecutionNode = {
            id: `node-${subProblem.id}`,
            subProblemId: subProblem.id,
            phase,
            canRunInParallel: subProblem.type === 'parallel',
            dependencies: subProblem.dependencies,
            estimatedStartTime: phase * 2, // Simplified calculation
            estimatedEndTime: phase * 2 + subProblem.estimatedTime
          };
          
          nodes.push(node);
          processed.add(subProblem.id);
          
          if (!phases.has(phase)) {
            phases.set(phase, []);
          }
          phases.get(phase)!.push(subProblem.id);
        }
      }
    }
    
    return nodes.sort((a, b) => a.phase - b.phase);
  }

  private calculateTotalTime(executionPlan: ExecutionNode[]): number {
    if (executionPlan.length === 0) return 0;
    
    const phases = new Map<number, ExecutionNode[]>();
    
    // Group by phases
    for (const node of executionPlan) {
      if (!phases.has(node.phase)) {
        phases.set(node.phase, []);
      }
      phases.get(node.phase)!.push(node);
    }
    
    // Calculate time for each phase (parallel execution within phase)
    let totalTime = 0;
    for (const [phase, nodes] of phases) {
      const maxTimeInPhase = Math.max(...nodes.map(n => n.estimatedEndTime - n.estimatedStartTime));
      totalTime += maxTimeInPhase;
    }
    
    return totalTime;
  }

  private findCriticalPath(executionPlan: ExecutionNode[]): string[] {
    // Simple critical path algorithm
    const path: string[] = [];
    const nodeMap = new Map(executionPlan.map(n => [n.subProblemId, n]));
    
    // Find the node with the latest end time
    let currentNode = executionPlan.reduce((latest, node) => 
      node.estimatedEndTime > latest.estimatedEndTime ? node : latest
    );
    
    // Trace back through dependencies
    while (currentNode) {
      path.unshift(currentNode.subProblemId);
      
      if (currentNode.dependencies.length === 0) break;
      
      // Find the dependency with the latest end time
      const dependentNodes = currentNode.dependencies
        .map(depId => nodeMap.get(depId))
        .filter((node): node is ExecutionNode => node !== undefined);
        
      if (dependentNodes.length > 0) {
        currentNode = dependentNodes.reduce((latest, node) => 
            node.estimatedEndTime > latest.estimatedEndTime ? node : latest
        );
      } else {
        break;
      }
    }
    
    return path;
  }

  private performRiskAssessment(problem: Problem, subProblems: SubProblem[]): RiskAssessment {
    const riskFactors: RiskFactor[] = [];
    
    // Analyze complexity risks
    const highComplexityProblems = subProblems.filter(sp => sp.estimatedComplexity > 6);
    if (highComplexityProblems.length > 0) {
      riskFactors.push({
        id: 'high-complexity',
        description: `${highComplexityProblems.length} sub-problems have high complexity`,
        probability: 0.7,
        impact: 0.8,
        category: 'technical',
        mitigation: 'Break down complex sub-problems further'
      });
    }
    
    // Analyze dependency risks
    const longDependencyChains = this.findLongDependencyChains(subProblems);
    if (longDependencyChains.length > 3) {
      riskFactors.push({
        id: 'dependency-complexity',
        description: 'Long dependency chains may cause delays',
        probability: 0.6,
        impact: 0.7,
        category: 'time',
        mitigation: 'Identify opportunities for parallel execution'
      });
    }
    
    // Analyze resource risks
    const uniqueResources = new Set(subProblems.flatMap(sp => sp.requiredResources));
    if (uniqueResources.size > 10) {
      riskFactors.push({
        id: 'resource-dependency',
        description: 'High number of different resources required',
        probability: 0.5,
        impact: 0.6,
        category: 'resource',
        mitigation: 'Ensure resource availability and plan for substitutions'
      });
    }
    
    const overallRisk = this.calculateOverallRisk(riskFactors);
    const mitigationStrategies = this.generateMitigationStrategies(riskFactors);
    
    return {
      overallRisk,
      riskFactors,
      mitigationStrategies,
      contingencyPlan: this.createContingencyPlan(problem, riskFactors)
    };
  }

  private findLongDependencyChains(subProblems: SubProblem[]): string[][] {
    const chains: string[][] = [];
    const visited = new Set<string>();
    
    const findChain = (startId: string, currentChain: string[]): void => {
      if (visited.has(startId)) return;
      visited.add(startId);
      
      const current = subProblems.find(sp => sp.id === startId);
      if (!current) return;
      
      currentChain.push(startId);
      
      if (current.dependencies.length === 0) {
        if (currentChain.length > 3) {
          chains.push([...currentChain]);
        }
      } else {
        for (const depId of current.dependencies) {
          findChain(depId, [...currentChain]);
        }
      }
    };
    
    for (const subProblem of subProblems) {
      if (!visited.has(subProblem.id)) {
        findChain(subProblem.id, []);
      }
    }
    
    return chains;
  }

  private calculateOverallRisk(riskFactors: RiskFactor[]): 'low' | 'medium' | 'high' | 'critical' {
    if (riskFactors.length === 0) return 'low';
    
    const avgRisk = riskFactors.reduce((sum, rf) => sum + rf.probability * rf.impact, 0) / riskFactors.length;
    
    if (avgRisk > 0.7) return 'critical';
    if (avgRisk > 0.5) return 'high';
    if (avgRisk > 0.3) return 'medium';
    return 'low';
  }

  private generateMitigationStrategies(riskFactors: RiskFactor[]): MitigationStrategy[] {
    return riskFactors.map(rf => ({
      riskId: rf.id,
      strategy: rf.mitigation || 'Monitor and adapt as needed',
      cost: rf.impact * 100, // Simplified cost calculation
      effectiveness: 0.7, // Default effectiveness
      timeRequired: rf.probability * 10 // Simplified time calculation
    }));
  }

  private createContingencyPlan(problem: Problem, riskFactors: RiskFactor[]): string[] {
    const plan = ['Monitor progress closely', 'Regular checkpoint reviews'];
    
    if (riskFactors.some(rf => rf.category === 'time')) {
      plan.push('Prepare scope reduction options');
      plan.push('Identify fast-track alternatives');
    }
    
    if (riskFactors.some(rf => rf.category === 'resource')) {
      plan.push('Maintain resource backup list');
      plan.push('Cross-train team members');
    }
    
    if (riskFactors.some(rf => rf.category === 'technical')) {
      plan.push('Prepare proof-of-concept validation');
      plan.push('Identify technical alternatives');
    }
    
    return plan;
  }

  private generateRecommendations(problem: Problem, subProblems: SubProblem[], riskAssessment: RiskAssessment): string[] {
    const recommendations: string[] = [];
    
    // General recommendations
    recommendations.push('Start with highest-risk sub-problems to validate approaches early');
    recommendations.push('Maintain regular communication with stakeholders');
    
    // Complexity-based recommendations
    const avgComplexity = subProblems.reduce((sum, sp) => sum + sp.estimatedComplexity, 0) / subProblems.length;
    if (avgComplexity > 5) {
      recommendations.push('Consider prototyping for complex sub-problems');
      recommendations.push('Plan for additional buffer time due to high complexity');
    }
    
    // Risk-based recommendations
    if (riskAssessment.overallRisk === 'high' || riskAssessment.overallRisk === 'critical') {
      recommendations.push('Implement frequent milestone reviews');
      recommendations.push('Consider reducing scope to manage risks');
    }
    
    // Resource-based recommendations
    const totalResources = new Set(subProblems.flatMap(sp => sp.requiredResources)).size;
    if (totalResources > 8) {
      recommendations.push('Ensure resource coordination and scheduling');
      recommendations.push('Consider resource sharing opportunities');
    }
    
    return recommendations;
  }
}
