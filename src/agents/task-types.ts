/**
 * Common types for Claude Code Task Tool integration
 */

export interface TaskRequestContext {
  validationTaskType?: string;
  strict?: boolean;
  sources?: string | string[];
  /**
   * Phase-specific state. UI generation currently accepts `entities`.
   */
  phaseState?: unknown;
  /**
   * UI scaffold output root. The CodeX adapter accepts only repository-relative,
   * non-traversing paths before any filesystem writes are allowed.
   */
  outputDir?: string;
  /**
   * Explicit operator approval for trusted write-capable phases.
   */
  approval?: {
    approved?: boolean;
    scope?: string;
    actor?: string;
    reason?: string;
  };
  /**
   * When true, phases that support it must avoid writing generated files.
   */
  dryRun?: boolean;
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
  // Formal phase separates generated scaffolds from real checker execution.
  formal?: {
    scaffold: {
      status: 'generated';
      artifactStatus: 'draft';
      validationStatus: 'valid' | 'invalid' | 'pending';
      artifactPath?: string;
    };
    modelChecking: {
      status: 'not-run';
      evidenceArtifact: null;
      runnerCommands: string[];
    };
  };
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
