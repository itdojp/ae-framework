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
  // Short status line. Blocked responses should start with "Blocked:".
  summary: string;
  // Main analysis body for humans/agents.
  analysis: string;
  // Optional supporting recommendations.
  recommendations: string[];
  // Deterministic next steps. When unblocked, at least one actionable item is required.
  nextActions: string[];
  // Non-empty for blocked responses; first item should describe minimal human action.
  warnings: string[];
  shouldBlockProgress: boolean;
  // Machine-readable blocker key for deterministic retries.
  blockingReason?: string;
  // Minimal input required to resume execution (tool-neutral string format).
  requiredHumanInput?: string;
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
