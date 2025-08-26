import { TaskHandler, TaskRequest, TaskResponse } from './task-types.js';
import { IntentTaskAdapter } from './intent-task-adapter.js';
import { NaturalLanguageTaskAdapter } from './natural-language-task-adapter.js';
import { UserStoriesTaskAdapter } from './user-stories-task-adapter.js';
import { ValidationTaskAdapter } from './validation-task-adapter.js';
import { DomainModelingTaskAdapter } from './domain-modeling-task-adapter.js';
import { UIScaffoldGenerator } from '../generators/ui-scaffold-generator.js';

// CodeX Task Adapter (skeleton)
// Maps CodeX tasks to ae-framework Phase 1–6 handlers.

type Phase = 'intent' | 'formal' | 'stories' | 'validation' | 'modeling' | 'ui';

export interface CodexTaskAdapterOptions {
  // Future: inject concrete phase handlers if needed
  // e.g., naturalLanguageHandler, userStoriesHandler, ...
}

export function createCodexTaskAdapter(_opts: CodexTaskAdapterOptions = {}): TaskHandler {
  const intent = new IntentTaskAdapter();
  const nl = new NaturalLanguageTaskAdapter();
  const stories = new UserStoriesTaskAdapter();
  const validation = new ValidationTaskAdapter();
  const modeling = new DomainModelingTaskAdapter();
  const handler: TaskHandler = {
    async handleTask(request: TaskRequest): Promise<TaskResponse> {
      const phase = selectPhase(request);
      try {
        switch (phase) {
          case 'intent':
            return await intent.handleIntentTask(request as any);
          case 'formal':
            // Map formal → natural language/spec processing for now
            return await nl.handleNaturalLanguageTask(request);
          case 'stories':
            return await stories.handleUserStoriesTask(request);
          case 'validation':
            return await validation.handleValidationTask(request);
          case 'modeling':
            return await modeling.handleDomainModelingTask(request);
          case 'ui':
            return await handleUI(request);
          default:
            return neutralResponse(phase, request);
        }
      } catch (err) {
        return {
          summary: `CodeX adapter error in phase: ${phase}`,
          analysis: String(err),
          recommendations: recommendNextActions(phase),
          nextActions: [],
          warnings: ['Adapter error encountered'],
          shouldBlockProgress: true,
        };
      }
    },
    async provideProactiveGuidance(context) {
      const actions: string[] = [];
      const recent = (context.recentFiles || []).join(', ');
      const msg: string[] = [];

      if (!(context.userIntent || '').trim()) {
        actions.push('Clarify user intent for the current task');
      }
      if (!recent) {
        actions.push('Run verify to generate baseline artifacts');
      }
      if (!actions.length) {
        actions.push('Proceed with next phase or run quality gates');
      }

      msg.push('CodeX adapter proactive guidance');
      if (recent) msg.push(`Recent files: ${recent}`);

      return {
        shouldIntervene: actions.length > 0,
        intervention: {
          type: 'suggestion',
          message: msg.join(' | '),
          recommendedActions: actions,
        },
      };
    }
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

async function handleUI(request: TaskRequest): Promise<TaskResponse> {
  const ctx = (request as any).context || {};
  const phaseState = ctx.phaseState;
  const outputDir = ctx.outputDir || 'apps';

  if (!phaseState?.entities || Object.keys(phaseState.entities).length === 0) {
    return {
      summary: 'UI generation skipped - no entities provided',
      analysis: 'Provide context.phaseState.entities to generate UI scaffolds.',
      recommendations: [
        'Populate context.phaseState.entities with domain entities',
        'Or run: ae ui-scaffold --components'
      ],
      nextActions: ['Run CLI-based ui-scaffold as a fallback'],
      warnings: [],
      shouldBlockProgress: false,
    };
  }

  const gen = new UIScaffoldGenerator(phaseState, { outputDir });
  const results = await gen.generateAll();
  const total = Object.values(results).length;
  const ok = Object.values(results).filter(r => r.success).length;
  const files = Object.values(results).flatMap(r => r.success ? (r.files || []) : []);

  return {
    summary: `UI scaffold complete: ${ok}/${total} entities` ,
    analysis: files.length ? files.map(f => `• ${f}`).join('\n') : 'No files generated',
    recommendations: ['Run quality gates for phase 6', 'Review a11y/performance metrics'],
    nextActions: ['pnpm run test:a11y', 'pnpm run test:coverage'],
    warnings: [],
    shouldBlockProgress: false,
  };
}

function neutralResponse(phase: Phase, request: TaskRequest): TaskResponse {
  const actions = recommendNextActions(phase);
  return {
    summary: `CodeX adapter received phase: ${phase}`,
    analysis: request.description || request.prompt || '',
    recommendations: actions,
    nextActions: actions,
    warnings: [],
    shouldBlockProgress: false,
  };
}
