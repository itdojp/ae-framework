import { TaskHandler, TaskRequest, TaskResponse } from './task-types.js';

// CodeX Task Adapter (skeleton)
// Maps CodeX tasks to ae-framework Phase 1–6 handlers.

type Phase = 'intent' | 'formal' | 'stories' | 'validation' | 'modeling' | 'ui';

export interface CodexTaskAdapterOptions {
  // Future: inject concrete phase handlers if needed
  // e.g., naturalLanguageHandler, userStoriesHandler, ...
}

export function createCodexTaskAdapter(_opts: CodexTaskAdapterOptions = {}): TaskHandler {
  const handler: TaskHandler = {
    async handleTask(request: TaskRequest): Promise<TaskResponse> {
      const phase = selectPhase(request);
      // For PoC: return a neutral response with recommended next actions.
      // Future: delegate to concrete phase handlers and collect real outputs.
      const actions = recommendNextActions(phase);
      return {
        summary: `CodeX adapter received phase: ${phase}`,
        analysis: request.description || request.prompt || '',
        recommendations: actions,
        nextActions: actions,
        warnings: [],
        shouldBlockProgress: false,
      };
    },
  };
  return handler;
}

function selectPhase(req: TaskRequest): Phase {
  const t = (req.subagent_type || req.description || req.prompt || '').toLowerCase();
  if (t.includes('intent')) return 'intent';
  if (t.includes('formal') || t.includes('spec')) return 'formal';
  if (t.includes('story') || t.includes('stories')) return 'stories';
  if (t.includes('validate') || t.includes('validation')) return 'validation';
  if (t.includes('model')) return 'modeling';
  if (t.includes('ui') || t.includes('frontend')) return 'ui';
  return 'intent';
}

function recommendNextActions(phase: Phase): string[] {
  switch (phase) {
    case 'intent':
      return [
        'Extract requirements and acceptance criteria',
        'Proceed to formal specification (Phase 2)'
      ];
    case 'formal':
      return [
        'Validate specification consistency',
        'Generate user stories (Phase 3)'
      ];
    case 'stories':
      return [
        'Derive test cases from user stories',
        'Run integration checks (Phase 4/5)'
      ];
    case 'validation':
      return [
        'Cross-validate requirements/stories/specs',
        'Prepare domain modeling (Phase 5)'
      ];
    case 'modeling':
      return [
        'Create domain entities and relationships',
        'Generate UI components (Phase 6)'
      ];
    case 'ui':
      return [
        'Run UI scaffold and quality gates',
        'Publish artifacts and telemetry'
      ];
    default:
      return [];
  }
}

