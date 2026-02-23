/**
 * Common types for Claude Code Task Tool integration
 */

export interface TaskRequestContext {
  validationTaskType?: string;
  strict?: boolean;
  sources?: string | string[];
  [key: string]: unknown;
}

export interface TaskRequest {
  description: string;
  prompt: string;
  subagent_type: string;
  context?: TaskRequestContext;
}

export interface TaskResponse {
  summary: string;
  analysis: string;
  recommendations: string[];
  nextActions: string[];
  warnings: string[];
  shouldBlockProgress: boolean;
}

export interface TaskHandler {
  handleTask: (request: TaskRequest) => Promise<TaskResponse>;
  provideProactiveGuidance?: (context: ProactiveGuidanceContext) => Promise<ProactiveGuidanceResult>;
}

export interface ProactiveGuidanceContext {
  recentFiles: string[];
  recentActions: string[];
  userIntent: string;
}

export interface ProactiveGuidanceResult {
  shouldIntervene: boolean;
  intervention: {
    type: 'warning' | 'suggestion' | 'block';
    message: string;
    recommendedActions: string[];
  };
}
