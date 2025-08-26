import { TaskHandler, TaskRequest, TaskResponse } from './task-types.js';
import { IntentTaskAdapter } from './intent-task-adapter.js';
import { NaturalLanguageTaskAdapter } from './natural-language-task-adapter.js';
import { UserStoriesTaskAdapter } from './user-stories-task-adapter.js';
import { ValidationTaskAdapter } from './validation-task-adapter.js';
import { DomainModelingTaskAdapter } from './domain-modeling-task-adapter.js';
import { UIScaffoldGenerator } from '../generators/ui-scaffold-generator.js';
import { FormalAgent } from './formal-agent.js';
import * as fs from 'fs';
import * as path from 'path';

type Phase = 'intent' | 'formal' | 'stories' | 'validation' | 'modeling' | 'ui';

export interface CodexTaskAdapterOptions {}

export function createCodexTaskAdapter(_opts: CodexTaskAdapterOptions = {}): TaskHandler {
  const intent = new IntentTaskAdapter();
  const nl = new NaturalLanguageTaskAdapter();
  const stories = new UserStoriesTaskAdapter();
  const validation = new ValidationTaskAdapter();
  const modeling = new DomainModelingTaskAdapter();
  const formal = new FormalAgent({ outputFormat: 'tla+', validationLevel: 'comprehensive', generateDiagrams: false, enableModelChecking: true });

  const handler: TaskHandler = {
    async handleTask(request: TaskRequest): Promise<TaskResponse> {
      const phase = selectPhase(request);
      try {
        switch (phase) {
          case 'intent':
            return writeAndReturn(phase, await intent.handleIntentTask(request as any));
          case 'formal': {
            const reqText = request.prompt || request.description || '';
            const spec = await formal.generateFormalSpecification(reqText, 'tla+');
            // Derive OpenAPI as a convenience artifact
            let openapiPath = '';
            try {
              const openapi = await formal.createAPISpecification(reqText, 'openapi', { includeExamples: true, generateContracts: true });
              const outDir = path.join(process.cwd(), 'artifacts', 'codex');
              fs.mkdirSync(outDir, { recursive: true });
              openapiPath = path.join(outDir, 'openapi.yaml');
              fs.writeFileSync(openapiPath, openapi.content, 'utf8');
            } catch {}
            return writeAndReturn(phase, {
              summary: `Formal spec generated: ${spec.type.toUpperCase()} (${spec.validation.status})`,
              analysis: spec.content.slice(0, 1200),
              recommendations: [
                'Validate properties',
                openapiPath ? `Review OpenAPI: ${path.relative(process.cwd(), openapiPath)}` : 'Consider API spec generation if needed'
              ],
              nextActions: ['Proceed to tests generation', 'Run model checking'],
              warnings: spec.validation.warnings?.map(w => w.message) || [],
              shouldBlockProgress: spec.validation.status === 'invalid',
            });
          }
          case 'stories':
            return writeAndReturn(phase, await stories.handleUserStoriesTask(request));
          case 'validation':
            return writeAndReturn(phase, await validation.handleValidationTask(request));
          case 'modeling':
            return writeAndReturn(phase, await modeling.handleDomainModelingTask(request));
          case 'ui':
            return writeAndReturn(phase, await handleUI(request));
          default:
            return writeAndReturn(phase, neutralResponse(phase, request));
        }
      } catch (err) {
        const errorResp: TaskResponse = {
          summary: `CodeX adapter error in phase: ${phase}`,
          analysis: String(err),
          recommendations: recommendNextActions(phase),
          nextActions: [],
          warnings: ['Adapter error encountered'],
          shouldBlockProgress: true,
        };
        return writeAndReturn(phase, errorResp);
      }
    },
    async provideProactiveGuidance(context) {
      const actions: string[] = [];
      const recent = (context.recentFiles || []).join(', ');
      const msg: string[] = [];

      if (!(context.userIntent || '').trim()) actions.push('Clarify user intent for the current task');
      if (!recent) actions.push('Run verify to generate baseline artifacts');
      if (!actions.length) actions.push('Proceed with next phase or run quality gates');

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
      return ['Extract requirements and acceptance criteria', 'Proceed to formal specification (Phase 2)'];
    case 'formal':
      return ['Validate specification consistency', 'Generate user stories (Phase 3)'];
    case 'stories':
      return ['Derive test cases from user stories', 'Run integration checks (Phase 4/5)'];
    case 'validation':
      return ['Cross-validate requirements/stories/specs', 'Prepare domain modeling (Phase 5)'];
    case 'modeling':
      return ['Create domain entities and relationships', 'Generate UI components (Phase 6)'];
    case 'ui':
      return ['Run UI scaffold and quality gates', 'Publish artifacts and telemetry'];
    default:
      return [];
  }
}

async function handleUI(request: TaskRequest): Promise<TaskResponse> {
  const ctx = (request as any).context || {};
  const phaseState = ctx.phaseState;
  const outputDir = ctx.outputDir || 'apps';

  let effectiveState = phaseState;
  let dryRun = false;
  if (!phaseState?.entities || Object.keys(phaseState.entities).length === 0) {
    dryRun = true;
    effectiveState = {
      entities: {
        demo: {
          description: 'Demo entity (dry-run)',
          attributes: {
            id: { type: 'uuid', required: true, description: 'ID' },
            name: { type: 'string', required: true, description: 'Name' },
            createdAt: { type: 'date', required: false, description: 'Created timestamp' }
          },
          acceptance_criteria: ['Name is required']
        }
      }
    } as any;
  }

  const gen = new UIScaffoldGenerator(effectiveState as any, { outputDir, dryRun });
  const results = await gen.generateAll();
  const total = Object.values(results).length;
  const ok = Object.values(results).filter(r => r.success).length;
  const files = Object.values(results).flatMap(r => r.success ? (r.files || []) : []);

  return {
    summary: `UI scaffold ${dryRun ? '(dry-run) ' : ''}complete: ${ok}/${total} entities` ,
    analysis: files.length ? files.map(f => `• ${f}`).join('\n') : 'No files generated',
    recommendations: [
      dryRun ? 'Provide context.phaseState.entities to generate real files' : 'Run quality gates for phase 6',
      'Review a11y/performance metrics'
    ],
    nextActions: ['pnpm run test:a11y', 'pnpm run test:coverage'],
    warnings: [],
    shouldBlockProgress: false,
  };
}

function writeAndReturn(phase: Phase, response: TaskResponse): TaskResponse {
  try {
    const outDir = path.join(process.cwd(), 'artifacts', 'codex');
    fs.mkdirSync(outDir, { recursive: true });
    const file = path.join(outDir, `result-${phase}.json`);
    fs.writeFileSync(file, JSON.stringify({ phase, response, ts: new Date().toISOString() }, null, 2), 'utf8');
  } catch {
    // best-effort only
  }
  return response;
}
