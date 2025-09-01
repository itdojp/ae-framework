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
import { trace } from '@opentelemetry/api';
import { z } from 'zod';

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
      const tracer = trace.getTracer('ae-codex-adapter');
      const span = tracer.startSpan('codex.adapter.handleTask', {
        attributes: {
          'ae.phase': phase,
          'ae.codex.adapter': true,
        },
      });
      try {
        switch (phase) {
          case 'intent':
            {
              const resp = await intent.handleIntentTask(request as any);
              span.setAttributes({ 'ae.result.blocked': resp.shouldBlockProgress || false, 'ae.result.warnings': resp.warnings?.length || 0 });
              return writeAndReturn(phase, resp);
            }
          case 'formal': {
            const reqText = request.prompt || request.description || '';
            const spec = await formal.generateFormalSpecification(reqText, 'tla+');
            // Derive OpenAPI as a convenience artifact
            let openapiPath = '';
            let tlaPath = '';
            let mcPath = '';
            try {
              // write TLA+ spec content
              const outDir = getArtifactsDir();
              fs.mkdirSync(outDir, { recursive: true });
              tlaPath = path.join(outDir, 'formal.tla');
              fs.writeFileSync(tlaPath, spec.content, 'utf8');

              const openapi = await formal.createAPISpecification(reqText, 'openapi', { includeExamples: true, generateContracts: true });
              openapiPath = path.join(outDir, 'openapi.yaml');
              fs.writeFileSync(openapiPath, openapi.content, 'utf8');

              // Model checking (best-effort)
              try {
                const mc = await formal.runModelChecking(spec, []);
                mcPath = path.join(outDir, 'model-check.json');
                fs.writeFileSync(mcPath, JSON.stringify(mc, null, 2), 'utf8');
              } catch {}
            } catch {}
            const resp: TaskResponse = {
              summary: `Formal spec generated: ${spec.type.toUpperCase()} (${spec.validation.status})`,
              analysis: spec.content.slice(0, 1200),
              recommendations: [
                'Validate properties',
                tlaPath ? `Review TLA+: ${path.relative(process.cwd(), tlaPath)}` : 'TLA+ content available in response',
                openapiPath ? `Review OpenAPI: ${path.relative(process.cwd(), openapiPath)}` : 'Consider API spec generation if needed',
                mcPath ? `Check model checking: ${path.relative(process.cwd(), mcPath)}` : 'Model checking unavailable'
              ],
              nextActions: ['Proceed to tests generation', 'Run model checking'],
              warnings: spec.validation.warnings?.map(w => w.message) || [],
              shouldBlockProgress: spec.validation.status === 'invalid',
            };
            span.setAttributes({ 'ae.result.blocked': resp.shouldBlockProgress || false, 'ae.result.warnings': resp.warnings?.length || 0 });
            return writeAndReturn(phase, resp);
          }
          case 'stories':
            {
              const resp = await stories.handleUserStoriesTask(request);
              span.setAttributes({ 'ae.result.blocked': resp.shouldBlockProgress || false, 'ae.result.warnings': resp.warnings?.length || 0 });
              return writeAndReturn(phase, resp);
            }
          case 'validation':
            {
              const resp = await validation.handleValidationTask(request);
              span.setAttributes({ 'ae.result.blocked': resp.shouldBlockProgress || false, 'ae.result.warnings': resp.warnings?.length || 0 });
              return writeAndReturn(phase, resp);
            }
          case 'modeling':
            {
              const resp = await modeling.handleDomainModelingTask(request);
              span.setAttributes({ 'ae.result.blocked': resp.shouldBlockProgress || false, 'ae.result.warnings': resp.warnings?.length || 0 });
              return writeAndReturn(phase, resp);
            }
          case 'ui':
            {
              const resp = await handleUI(request, span);
              span.setAttributes({ 'ae.result.blocked': resp.shouldBlockProgress || false, 'ae.result.warnings': resp.warnings?.length || 0 });
              return writeAndReturn(phase, resp);
            }
          default:
            return writeAndReturn(phase, createNeutralResponse(phase, request));
        }
      } catch (err) {
        span.recordException(err as Error);
        const errorResp: TaskResponse = {
          summary: `CodeX adapter error in phase: ${phase}`,
          analysis: String(err),
          recommendations: recommendNextActions(phase),
          nextActions: [],
          warnings: ['Adapter error encountered'],
          shouldBlockProgress: true,
        };
        return writeAndReturn(phase, errorResp);
      } finally {
        span.end();
      }
    },
    async provideProactiveGuidance(context) {
      const actions: string[] = [];
      const recentFiles = context.recentFiles || [];
      const recent = recentFiles.join(', ');
      const msg: string[] = [];

      const intent = (context.userIntent || '').toLowerCase();
      const hasOpenAPI = recentFiles.some(f => f.includes('openapi.yaml'));
      const hasTLA = recentFiles.some(f => f.endsWith('.tla'));
      const hasUISummary = recentFiles.some(f => f.includes('ui-summary.json'));

      if (!intent.trim()) actions.push('Clarify user intent for the current task');
      if (!recent) actions.push('Run verify to generate baseline artifacts');

      // Phase-aware nudges
      if (intent.includes('api') || hasOpenAPI) {
        actions.push('Generate/validate API specs (OpenAPI)');
        actions.push('Derive contract tests from API specs');
      }
      if (hasTLA) {
        actions.push('Run model checking on TLA+');
        actions.push('Review properties and counterexamples');
      }
      if (hasUISummary) {
        actions.push('Run accessibility and coverage gates for UI');
      }
      if (!actions.length) actions.push('Proceed with next phase or run quality gates');

      msg.push('CodeX adapter proactive guidance');
      if (recent) msg.push(`Recent files: ${recent}`);

      return {
        shouldIntervene: actions.length > 0,
        intervention: {
          type: 'suggestion',
          message: msg.join(' | '),
          recommendedActions: Array.from(new Set(actions)),
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

async function handleUI(request: TaskRequest, parentSpan?: any): Promise<TaskResponse> {
  const ctx = (request as any).context || {};
  const phaseState = ctx.phaseState;
  const outputDir = ctx.outputDir || 'apps';

  let effectiveState = phaseState;
  // Resolve dryRun precedence: context.dryRun > CODEX_UI_DRY_RUN env > fallback
  let dryRun: boolean | undefined = typeof ctx.dryRun === 'boolean' ? ctx.dryRun : undefined;
  if (dryRun === undefined) {
    const env = process.env.CODEX_UI_DRY_RUN;
    if (env === '0') dryRun = false;
    else if (env === '1') dryRun = true;
  }
  if (dryRun === undefined && (!phaseState?.entities || Object.keys(phaseState.entities).length === 0)) {
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

  const tracer = trace.getTracer('ae-codex-adapter');
  const span = tracer.startSpan('codex.adapter.ui', { attributes: { 'ae.phase': 'ui', 'ae.ui.dryRun': !!dryRun } });

  // Runtime schema validation
  const AttributeSchema = z.object({
    type: z.string(),
    required: z.boolean().optional(),
    description: z.string().optional(),
  });
  const EntitySchema = z.object({
    description: z.string().optional(),
    attributes: z.record(AttributeSchema),
    acceptance_criteria: z.array(z.string()).optional(),
  });
  const PhaseStateSchema = z.object({
    entities: z.record(EntitySchema),
  });

  if (effectiveState) {
    const parsed = PhaseStateSchema.safeParse(effectiveState);
    if (!parsed.success) {
      const msgs = parsed.error.issues.map(i => `${i.path.join('.')}: ${i.message}`);
      const resp: TaskResponse = {
        summary: 'Invalid Phase 6 phaseState input',
        analysis: msgs.join('\n'),
        recommendations: [
          'Fix phaseState.entities schema (see analysis)',
          'Provide valid attribute types and required flags',
        ],
        nextActions: ['Re-run UI generation after fixing inputs'],
        warnings: msgs,
        shouldBlockProgress: true,
      };
      span.setAttributes({ 'ae.result.blocked': true, 'ae.result.warnings': msgs.length });
      span.end();
      return resp;
    }
  }
  const gen = new UIScaffoldGenerator(effectiveState as any, { outputDir, dryRun });
  const results = await gen.generateAll();
  const total = Object.values(results).length;
  const ok = Object.values(results).filter(r => r.success).length;
  const files = Object.values(results).flatMap(r => r.success ? (r.files || []) : []);
  span.setAttributes({ 'ae.ui.entities.total': total, 'ae.ui.entities.ok': ok, 'ae.ui.files.count': files.length });

  // Write additional UI summary artifact (machine-readable)
  try {
    const outDir = getArtifactsDir();
    fs.mkdirSync(outDir, { recursive: true });
    const uiSummaryPath = path.join(outDir, 'ui-summary.json');
    fs.writeFileSync(uiSummaryPath, JSON.stringify({ totalEntities: total, okEntities: ok, files, dryRun, artifactDir: outDir }, null, 2), 'utf8');
  } catch {}

  const resp: TaskResponse = {
    summary: `UI scaffold ${dryRun ? '(dry-run) ' : ''}complete: ${ok}/${total} entities` ,
    analysis: files.length ? files.map(f => `• ${f}`).join('\n') : 'No files generated',
    recommendations: [
      dryRun ? 'Provide context.phaseState.entities to generate real files' : `Files generated: ${files.length}`,
      'Review a11y/performance metrics'
    ],
    nextActions: ['pnpm run test:a11y', 'pnpm run test:coverage'],
    warnings: [],
    shouldBlockProgress: false,
  };
  span.end();
  return resp;
}

function writeAndReturn(phase: Phase, response: TaskResponse): TaskResponse {
  try {
    const outDir = getArtifactsDir();
    fs.mkdirSync(outDir, { recursive: true });
    const file = path.join(outDir, `result-${phase}.json`);
    fs.writeFileSync(file, JSON.stringify({ phase, response, ts: new Date().toISOString() }, null, 2), 'utf8');
  } catch {
    // best-effort only
  }
  return response;
}

function createNeutralResponse(phase: Phase, request: TaskRequest): TaskResponse {
  return {
    summary: `No specific handler available for phase: ${phase}`,
    analysis: `Task request received for phase '${phase}' but no specialized handler is implemented. Task type: ${(request as any).type || 'unknown'}`,
    recommendations: [`Implement specific handler for phase '${phase}'`, 'Consider using a different phase for this task type'],
    nextActions: ['Review task requirements', 'Select appropriate phase or implement handler'],
    warnings: [`Phase '${phase}' not fully supported in current implementation`],
    shouldBlockProgress: false
  };
}

function getArtifactsDir() {
  return process.env.CODEX_ARTIFACTS_DIR?.trim()
    ? path.resolve(process.env.CODEX_ARTIFACTS_DIR)
    : path.join(process.cwd(), 'artifacts', 'codex');
}
