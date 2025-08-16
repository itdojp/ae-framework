/**
 * User Stories Task Adapter for Claude Code
 * 
 * This adapter integrates Phase 3 (User Stories Creation) processing
 * with Claude Code's Task tool, enabling seamless user story generation,
 * validation, and management workflows.
 */

import { FormalAgent, FormalAgentConfig } from './formal-agent.js';

export interface TaskRequest {
  description: string;
  prompt: string;
  subagent_type: string;
}

export interface TaskResponse {
  summary: string;
  analysis: string;
  recommendations: string[];
  nextActions: string[];
  warnings: string[];
  shouldBlockProgress: boolean;
}

export interface UserStory {
  id: string;
  title: string;
  description: string;
  asA: string;
  iWant: string;
  soThat: string;
  acceptanceCriteria: string[];
  priority: 'high' | 'medium' | 'low';
  storyPoints: number;
  epic?: string;
  dependencies: string[];
  testScenarios: string[];
}

export interface UserStorySet {
  stories: UserStory[];
  epics: string[];
  totalStoryPoints: number;
  completenessScore: number;
  gaps: string[];
  conflicts: string[];
}

export class UserStoriesTaskAdapter {
  private agent: FormalAgent;

  constructor() {
    const config: FormalAgentConfig = {
      outputFormat: 'openapi',
      validationLevel: 'comprehensive',
      generateDiagrams: true,
      enableModelChecking: true,
    };

    this.agent = new FormalAgent(config);
  }

  /**
   * Main handler for User Stories tasks from Claude Code
   */
  async handleUserStoriesTask(request: TaskRequest): Promise<TaskResponse> {
    const taskType = this.classifyTask(request.description, request.prompt);
    
    switch (taskType) {
      case 'generate-stories':
        return this.handleStoryGeneration(request);
      
      case 'validate-stories':
        return this.handleStoryValidation(request);
      
      case 'prioritize-stories':
        return this.handleStoryPrioritization(request);
      
      case 'estimate-stories':
        return this.handleStoryEstimation(request);
      
      case 'create-acceptance-criteria':
        return this.handleAcceptanceCriteriaCreation(request);
      
      case 'organize-epics':
        return this.handleEpicOrganization(request);
      
      case 'identify-dependencies':
        return this.handleDependencyIdentification(request);
      
      default:
        return this.handleGenericStoryProcessing(request);
    }
  }

  /**
   * Proactive user story guidance for Claude Code
   */
  async provideProactiveGuidance(context: {
    recentFiles: string[];
    recentActions: string[];
    userIntent: string;
  }): Promise<{
    shouldIntervene: boolean;
    intervention: {
      type: 'warning' | 'suggestion' | 'block';
      message: string;
      recommendedActions: string[];
    };
  }> {
    const analysis = await this.analyzeRecentActivity(context);
    
    if (analysis.hasIncompleteStories) {
      return {
        shouldIntervene: true,
        intervention: {
          type: 'warning',
          message: 'Incomplete user stories detected - ensure all stories have proper acceptance criteria',
          recommendedActions: analysis.completionActions,
        },
      };
    }

    if (analysis.hasPoorStoryQuality) {
      return {
        shouldIntervene: true,
        intervention: {
          type: 'suggestion',
          message: 'User story quality can be improved - consider better structure and clarity',
          recommendedActions: analysis.qualityActions,
        },
      };
    }

    return {
      shouldIntervene: false,
      intervention: {
        type: 'suggestion',
        message: 'User stories are well-structured and complete',
        recommendedActions: [],
      },
    };
  }

  private async handleStoryGeneration(request: TaskRequest): Promise<TaskResponse> {
    const requirementsInput = this.extractRequirementsInput(request.prompt);
    const storySet = await this.generateUserStories(requirementsInput);
    
    return {
      summary: `User Story Generation Complete - ${storySet.stories.length} stories created across ${storySet.epics.length} epics`,
      analysis: `
# User Stories Generation Report

**Total Stories**: ${storySet.stories.length}
**Total Epics**: ${storySet.epics.length}
**Total Story Points**: ${storySet.totalStoryPoints}
**Completeness Score**: ${storySet.completenessScore}%

## Epic Breakdown
${storySet.epics.map((epic: string) => {
  const epicStories = storySet.stories.filter((s: UserStory) => s.epic === epic);
  return `• **${epic}**: ${epicStories.length} stories (${epicStories.reduce((sum: number, s: UserStory) => sum + s.storyPoints, 0)} points)`;
}).join('\n')}

## Priority Distribution
- **High Priority**: ${storySet.stories.filter((s: UserStory) => s.priority === 'high').length} stories
- **Medium Priority**: ${storySet.stories.filter((s: UserStory) => s.priority === 'medium').length} stories
- **Low Priority**: ${storySet.stories.filter((s: UserStory) => s.priority === 'low').length} stories

## Identified Gaps
${storySet.gaps.map((gap: string) => `• ${gap}`).join('\n')}
      `.trim(),
      recommendations: [
        'Review generated stories for completeness',
        'Validate acceptance criteria with stakeholders',
        'Consider story dependencies for sprint planning',
        'Estimate story points with development team',
      ],
      nextActions: [
        'Create detailed acceptance criteria for each story',
        'Define test scenarios based on stories',
        'Proceed to sprint planning and prioritization',
      ],
      warnings: storySet.gaps.length > 0 ? ['Story gaps detected - may affect feature coverage'] : [],
      shouldBlockProgress: storySet.completenessScore < 70,
    };
  }

  private async handleStoryValidation(request: TaskRequest): Promise<TaskResponse> {
    const storiesInput = this.extractStoriesInput(request.prompt);
    const validation = await this.validateUserStories(storiesInput);
    
    return {
      summary: `Story Validation Complete - ${validation.validStories}/${validation.totalStories} stories are valid`,
      analysis: `
# User Story Validation Report

**Valid Stories**: ${validation.validStories}/${validation.totalStories}
**Validation Score**: ${Math.round((validation.validStories / validation.totalStories) * 100)}%

## Validation Issues
${validation.issues.map((issue: any) => `• **${issue.story}**: ${issue.problem} - ${issue.severity}`).join('\n')}

## Quality Metrics
- **Proper Format**: ${validation.metrics.properFormat}%
- **Clear Acceptance Criteria**: ${validation.metrics.clearCriteria}%
- **Testable Stories**: ${validation.metrics.testable}%
- **Independent Stories**: ${validation.metrics.independent}%
      `.trim(),
      recommendations: validation.recommendations,
      nextActions: [
        'Fix validation issues in failed stories',
        'Improve acceptance criteria clarity',
        'Ensure all stories are testable and independent',
      ],
      warnings: validation.criticalIssues.map((issue: any) => issue.description),
      shouldBlockProgress: validation.criticalIssues.length > 0,
    };
  }

  private async handleStoryPrioritization(request: TaskRequest): Promise<TaskResponse> {
    const storiesInput = this.extractStoriesInput(request.prompt);
    const prioritization = await this.prioritizeUserStories(storiesInput);
    
    return {
      summary: `Story Prioritization Complete - ${prioritization.stories.length} stories prioritized`,
      analysis: `
# User Story Prioritization Report

**Total Stories**: ${prioritization.stories.length}

## Priority Matrix
${prioritization.priorityMatrix.map((group: any) => 
  `• **${group.priority}**: ${group.stories.length} stories (${group.businessValue} business value)`
).join('\n')}

## Release Recommendations
${prioritization.releases.map((release: any) => 
  `• **${release.name}**: ${release.stories.length} stories (${release.duration} weeks)`
).join('\n')}

## Business Value Analysis
- **High Value**: ${prioritization.businessValueDistribution.high} stories
- **Medium Value**: ${prioritization.businessValueDistribution.medium} stories
- **Low Value**: ${prioritization.businessValueDistribution.low} stories
      `.trim(),
      recommendations: [
        'Review priority assignments with product owner',
        'Consider dependencies in release planning',
        'Validate business value assessments',
      ],
      nextActions: [
        'Create release plan based on priorities',
        'Define sprint goals aligned with priorities',
        'Communicate priority rationale to team',
      ],
      warnings: prioritization.risks.map((risk: any) => risk.description),
      shouldBlockProgress: false,
    };
  }

  private async handleStoryEstimation(request: TaskRequest): Promise<TaskResponse> {
    const storiesInput = this.extractStoriesInput(request.prompt);
    const estimation = await this.estimateUserStories(storiesInput);
    
    return {
      summary: `Story Estimation Complete - ${estimation.totalStoryPoints} total story points estimated`,
      analysis: `
# User Story Estimation Report

**Total Story Points**: ${estimation.totalStoryPoints}
**Average Points per Story**: ${Math.round(estimation.averagePoints * 10) / 10}

## Estimation Distribution
${estimation.distribution.map((bucket: any) => 
  `• **${bucket.points} points**: ${bucket.count} stories`
).join('\n')}

## Complexity Analysis
- **Simple Stories (1-3 points)**: ${estimation.complexityBreakdown.simple} stories
- **Medium Stories (5-8 points)**: ${estimation.complexityBreakdown.medium} stories
- **Complex Stories (13+ points)**: ${estimation.complexityBreakdown.complex} stories

## Estimation Confidence
- **High Confidence**: ${estimation.confidence.high}%
- **Medium Confidence**: ${estimation.confidence.medium}%
- **Low Confidence**: ${estimation.confidence.low}%
      `.trim(),
      recommendations: [
        'Review high-point stories for potential breakdown',
        'Validate estimates with development team',
        'Consider re-estimating low-confidence stories',
      ],
      nextActions: [
        'Plan sprints based on team velocity and estimates',
        'Break down complex stories if needed',
        'Track actual vs estimated effort for calibration',
      ],
      warnings: estimation.concerns.map((concern: any) => concern.description),
      shouldBlockProgress: false,
    };
  }

  private async handleAcceptanceCriteriaCreation(request: TaskRequest): Promise<TaskResponse> {
    const storyInput = this.extractStoryInput(request.prompt);
    const criteria = await this.createAcceptanceCriteria(storyInput);
    
    return {
      summary: `Acceptance Criteria Created - ${criteria.criteria.length} criteria defined`,
      analysis: `
# Acceptance Criteria Report

**Total Criteria**: ${criteria.criteria.length}
**Story**: ${criteria.storyTitle}

## Generated Criteria
${criteria.criteria.map((criterion: any, index: number) => 
  `${index + 1}. **Given** ${criterion.given}, **When** ${criterion.when}, **Then** ${criterion.then}`
).join('\n')}

## Test Scenarios
${criteria.testScenarios.map((scenario: any, index: number) => 
  `${index + 1}. ${scenario.description} (${scenario.type})`
).join('\n')}

## Coverage Analysis
- **Happy Path**: ${criteria.coverage.happyPath}%
- **Edge Cases**: ${criteria.coverage.edgeCases}%
- **Error Handling**: ${criteria.coverage.errorHandling}%
      `.trim(),
      recommendations: [
        'Review criteria with stakeholders',
        'Ensure all edge cases are covered',
        'Validate testability of each criterion',
      ],
      nextActions: [
        'Create automated tests based on criteria',
        'Define manual testing scenarios',
        'Proceed to story implementation',
      ],
      warnings: criteria.gaps.map((gap: any) => gap.description),
      shouldBlockProgress: false,
    };
  }

  private async handleEpicOrganization(request: TaskRequest): Promise<TaskResponse> {
    const storiesInput = this.extractStoriesInput(request.prompt);
    const organization = await this.organizeStoriesIntoEpics(storiesInput);
    
    return {
      summary: `Epic Organization Complete - ${organization.epics.length} epics created`,
      analysis: `
# Epic Organization Report

**Total Epics**: ${organization.epics.length}
**Orphaned Stories**: ${organization.orphanedStories.length}

## Epic Breakdown
${organization.epics.map((epic: any) => 
  `• **${epic.name}**: ${epic.stories.length} stories (${epic.totalPoints} points, ${epic.estimatedWeeks} weeks)`
).join('\n')}

## Epic Dependencies
${organization.dependencies.map((dep: any) => 
  `• ${dep.from} → ${dep.to} (${dep.reason})`
).join('\n')}

## Release Mapping
${organization.releasePlan.map((release: any) => 
  `• **${release.name}**: ${release.epics.join(', ')} (${release.duration} weeks)`
).join('\n')}
      `.trim(),
      recommendations: [
        'Review epic definitions with product owner',
        'Consider epic dependencies in planning',
        'Assign orphaned stories to appropriate epics',
      ],
      nextActions: [
        'Create epic documentation',
        'Plan epic delivery order',
        'Define epic acceptance criteria',
      ],
      warnings: organization.orphanedStories.length > 0 ? ['Some stories are not assigned to epics'] : [],
      shouldBlockProgress: false,
    };
  }

  private async handleDependencyIdentification(request: TaskRequest): Promise<TaskResponse> {
    const storiesInput = this.extractStoriesInput(request.prompt);
    const dependencies = await this.identifyStoryDependencies(storiesInput);
    
    return {
      summary: `Dependency Analysis Complete - ${dependencies.totalDependencies} dependencies identified`,
      analysis: `
# Story Dependencies Report

**Total Dependencies**: ${dependencies.totalDependencies}
**Stories with Dependencies**: ${dependencies.dependentStories.length}

## Critical Dependencies
${dependencies.criticalPath.map((dep: any) => 
  `• **${dep.from}** → **${dep.to}** (${dep.type}: ${dep.reason})`
).join('\n')}

## Dependency Types
- **Technical Dependencies**: ${dependencies.byType.technical}
- **Business Dependencies**: ${dependencies.byType.business}
- **Data Dependencies**: ${dependencies.byType.data}
- **UI Dependencies**: ${dependencies.byType.ui}

## Risk Analysis
${dependencies.risks.map((risk: any) => 
  `• **${risk.severity}**: ${risk.description} (Impact: ${risk.impactedStories.length} stories)`
).join('\n')}
      `.trim(),
      recommendations: [
        'Plan development order based on dependencies',
        'Consider parallel development opportunities',
        'Address high-risk dependencies early',
      ],
      nextActions: [
        'Create dependency management plan',
        'Communicate dependencies to development team',
        'Monitor dependency resolution during development',
      ],
      warnings: dependencies.blockers.map((blocker: any) => blocker.description),
      shouldBlockProgress: dependencies.blockers.length > 2,
    };
  }

  private async handleGenericStoryProcessing(request: TaskRequest): Promise<TaskResponse> {
    const input = this.extractStoriesInput(request.prompt);
    const analysis = await this.performGenericStoryAnalysis(input);
    
    return {
      summary: 'General User Story Analysis',
      analysis: analysis.report,
      recommendations: analysis.recommendations,
      nextActions: analysis.nextActions,
      warnings: analysis.warnings,
      shouldBlockProgress: false,
    };
  }

  private classifyTask(description: string, prompt: string): string {
    const combined = (description + ' ' + prompt).toLowerCase();
    
    if (combined.includes('generate') || combined.includes('create stories') || combined.includes('write stories')) {
      return 'generate-stories';
    }
    
    if (combined.includes('validate') || combined.includes('check stories') || combined.includes('review')) {
      return 'validate-stories';
    }
    
    if (combined.includes('prioritize') || combined.includes('priority') || combined.includes('rank')) {
      return 'prioritize-stories';
    }
    
    if (combined.includes('estimate') || combined.includes('points') || combined.includes('sizing')) {
      return 'estimate-stories';
    }
    
    if (combined.includes('acceptance') || combined.includes('criteria') || combined.includes('conditions')) {
      return 'create-acceptance-criteria';
    }
    
    if (combined.includes('epic') || combined.includes('organize') || combined.includes('group')) {
      return 'organize-epics';
    }
    
    if (combined.includes('depend') || combined.includes('order') || combined.includes('sequence')) {
      return 'identify-dependencies';
    }
    
    return 'generic-processing';
  }

  private extractRequirementsInput(prompt: string): string {
    return prompt; // Simplified extraction
  }

  private extractStoriesInput(prompt: string): any {
    return {}; // Simplified extraction
  }

  private extractStoryInput(prompt: string): any {
    return {}; // Simplified extraction
  }

  // Mock implementations for demonstration
  private async generateUserStories(input: string): Promise<UserStorySet> {
    return {
      stories: [
        {
          id: 'US001',
          title: 'User Login',
          description: 'As a user, I want to log into the system so that I can access my account',
          asA: 'user',
          iWant: 'to log into the system',
          soThat: 'I can access my account',
          acceptanceCriteria: [
            'User can enter username and password',
            'System validates credentials',
            'User is redirected to dashboard on success',
          ],
          priority: 'high',
          storyPoints: 5,
          epic: 'User Management',
          dependencies: [],
          testScenarios: ['Valid login', 'Invalid credentials', 'Account locked'],
        },
      ],
      epics: ['User Management'],
      totalStoryPoints: 5,
      completenessScore: 85,
      gaps: ['Password reset functionality not specified'],
      conflicts: [],
    };
  }

  private async validateUserStories(input: any): Promise<any> {
    return {
      totalStories: 1,
      validStories: 1,
      issues: [],
      criticalIssues: [],
      recommendations: ['All stories are properly formatted'],
      metrics: {
        properFormat: 100,
        clearCriteria: 100,
        testable: 100,
        independent: 100,
      },
    };
  }

  private async prioritizeUserStories(input: any): Promise<any> {
    return {
      stories: [],
      priorityMatrix: [
        { priority: 'High', stories: [], businessValue: 'High' },
      ],
      releases: [
        { name: 'Release 1.0', stories: [], duration: 8 },
      ],
      businessValueDistribution: { high: 1, medium: 0, low: 0 },
      risks: [],
    };
  }

  private async estimateUserStories(input: any): Promise<any> {
    return {
      totalStoryPoints: 5,
      averagePoints: 5,
      distribution: [{ points: 5, count: 1 }],
      complexityBreakdown: { simple: 0, medium: 1, complex: 0 },
      confidence: { high: 100, medium: 0, low: 0 },
      concerns: [],
    };
  }

  private async createAcceptanceCriteria(input: any): Promise<any> {
    return {
      storyTitle: 'Sample Story',
      criteria: [
        {
          given: 'user has valid credentials',
          when: 'they submit login form',
          then: 'they should be logged in',
        },
      ],
      testScenarios: [
        { description: 'Valid login test', type: 'positive' },
      ],
      coverage: { happyPath: 100, edgeCases: 80, errorHandling: 70 },
      gaps: [],
    };
  }

  private async organizeStoriesIntoEpics(input: any): Promise<any> {
    return {
      epics: [
        {
          name: 'User Management',
          stories: [],
          totalPoints: 5,
          estimatedWeeks: 2,
        },
      ],
      orphanedStories: [],
      dependencies: [],
      releasePlan: [
        { name: 'Release 1.0', epics: ['User Management'], duration: 8 },
      ],
    };
  }

  private async identifyStoryDependencies(input: any): Promise<any> {
    return {
      totalDependencies: 0,
      dependentStories: [],
      criticalPath: [],
      byType: { technical: 0, business: 0, data: 0, ui: 0 },
      risks: [],
      blockers: [],
    };
  }

  private async performGenericStoryAnalysis(input: any): Promise<any> {
    return {
      report: 'General user story analysis completed',
      recommendations: ['Consider more detailed story breakdown'],
      nextActions: ['Proceed to story implementation'],
      warnings: [],
    };
  }

  private async analyzeRecentActivity(context: {
    recentFiles: string[];
    recentActions: string[];
    userIntent: string;
  }): Promise<{
    hasIncompleteStories: boolean;
    hasPoorStoryQuality: boolean;
    completionActions: string[];
    qualityActions: string[];
  }> {
    const storyFiles = context.recentFiles.filter((f: string) => 
      f.includes('story') || f.includes('stories') || f.includes('backlog')
    );
    
    const hasIncompleteStories = storyFiles.length === 0 && 
      context.userIntent.toLowerCase().includes('implement');
    
    const hasPoorStoryQuality = context.userIntent.includes('user') && 
      !context.userIntent.includes('acceptance criteria');
    
    return {
      hasIncompleteStories,
      hasPoorStoryQuality,
      completionActions: hasIncompleteStories ? [
        'Create comprehensive user stories',
        'Define clear acceptance criteria',
        'Estimate story complexity',
      ] : [],
      qualityActions: hasPoorStoryQuality ? [
        'Improve story structure and format',
        'Add detailed acceptance criteria',
        'Ensure stories are testable and independent',
      ] : [],
    };
  }
}

// Export for Claude Code Task tool integration
export const createUserStoriesTaskHandler = () => {
  const adapter = new UserStoriesTaskAdapter();
  
  return {
    handleTask: async (request: TaskRequest): Promise<TaskResponse> => {
      return adapter.handleUserStoriesTask(request);
    },
    
    provideProactiveGuidance: async (context: any): Promise<any> => {
      return adapter.provideProactiveGuidance(context);
    },
  };
};