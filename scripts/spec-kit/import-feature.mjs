#!/usr/bin/env node
import { existsSync, mkdirSync, readdirSync, readFileSync, statSync, writeFileSync } from 'node:fs';
import path from 'node:path';
import { createHash } from 'node:crypto';
import { pathToFileURL } from 'node:url';

const DEFAULT_FEATURE_DIR = 'fixtures/spec-kit/greenfield/specs/001-reservation-approval';
const DEFAULT_OUTPUT_DIR = 'artifacts/spec-kit';
const DEFAULT_GENERATED_AT = null;
const SCRIPT_NAME = 'scripts/spec-kit/import-feature.mjs';
const PASS = 'pass';
const WARNING = 'warning';
const FAIL = 'fail';

const SPEC_KIT_UPSTREAM = {
  repository: 'https://github.com/github/spec-kit',
  reference: 'main',
  verifiedPaths: [
    '.specify/memory/constitution.md',
    'templates/spec-template.md',
    'templates/plan-template.md',
    'templates/tasks-template.md',
    'templates/commands/specify.md',
    'templates/commands/plan.md',
    'templates/commands/tasks.md',
    'templates/commands/taskstoissues.md',
    'templates/commands/implement.md',
    'templates/commands/converge.md',
  ],
};

function toPosix(value) {
  return value.split(path.sep).join('/');
}

function normalizePathForReport(filePath, rootDir = process.cwd()) {
  const resolved = path.resolve(filePath);
  const relative = path.relative(path.resolve(rootDir), resolved);
  if (relative === '') return '.';
  return toPosix(relative && !relative.startsWith('..') ? relative : resolved);
}

function sha256(content) {
  return createHash('sha256').update(content).digest('hex');
}

function slugify(value, fallback = 'spec-kit-feature') {
  const slug = String(value || '')
    .trim()
    .toLowerCase()
    .replace(/[^a-z0-9]+/g, '-')
    .replace(/^-+|-+$/g, '');
  return slug || fallback;
}

function pascalCase(value, fallback = 'SpecKitFeature') {
  const words = slugify(value, fallback).split('-').filter(Boolean);
  const result = words.map((word) => word.charAt(0).toUpperCase() + word.slice(1)).join('');
  return result || fallback;
}

function titleFromSlug(value) {
  return slugify(value)
    .split('-')
    .filter(Boolean)
    .map((word) => word.charAt(0).toUpperCase() + word.slice(1))
    .join(' ');
}

function stripMarkdown(value) {
  return String(value || '')
    .replace(/`([^`]+)`/g, '$1')
    .replace(/\*\*([^*]+)\*\*/g, '$1')
    .replace(/__([^_]+)__/g, '$1')
    .replace(/\[([^\]]+)\]\([^)]+\)/g, '$1')
    .trim();
}

function normalizeLine(value) {
  return stripMarkdown(value).replace(/\s+/g, ' ').trim();
}

function parseArgs(argv = process.argv) {
  const args = argv.slice(2);
  const options = {
    projectRoot: '.',
    featureDir: DEFAULT_FEATURE_DIR,
    outputDir: DEFAULT_OUTPUT_DIR,
    reportJson: null,
    reportMd: null,
    contextPackJson: null,
    execPlanJson: null,
    generatedAt: DEFAULT_GENERATED_AT,
    sourceIssue: '#3550',
    repository: 'itdojp/ae-framework',
    noWrite: false,
    help: false,
  };

  for (let index = 0; index < args.length; index += 1) {
    const arg = args[index];
    if (arg === '--' && index === 0) continue;
    if (arg === '--') break;
    if (arg === '--help' || arg === '-h') {
      options.help = true;
      continue;
    }
    if (arg === '--no-write') {
      options.noWrite = true;
      continue;
    }
    const valueOptions = new Map([
      ['--project-root', 'projectRoot'],
      ['--work', 'projectRoot'],
      ['--feature-dir', 'featureDir'],
      ['--feature', 'featureDir'],
      ['--output-dir', 'outputDir'],
      ['--report-json', 'reportJson'],
      ['--output-json', 'reportJson'],
      ['--report-md', 'reportMd'],
      ['--output-md', 'reportMd'],
      ['--context-pack-json', 'contextPackJson'],
      ['--exec-plan-json', 'execPlanJson'],
      ['--generated-at', 'generatedAt'],
      ['--source-issue', 'sourceIssue'],
      ['--repo', 'repository'],
    ]);
    if (valueOptions.has(arg)) {
      const target = valueOptions.get(arg);
      const next = args[index + 1];
      if (!next || next.startsWith('--')) {
        throw new Error(`${arg} requires a value`);
      }
      options[target] = next;
      index += 1;
      continue;
    }
    throw new Error(`Unknown argument: ${arg}`);
  }

  return deriveOutputPaths(options);
}

function deriveOutputPaths(options) {
  const outputDir = options.outputDir || DEFAULT_OUTPUT_DIR;
  return {
    ...options,
    outputDir,
    reportJson: options.reportJson || path.join(outputDir, 'spec-kit-bridge-report.json'),
    reportMd: options.reportMd || path.join(outputDir, 'spec-kit-bridge-report.md'),
    contextPackJson: options.contextPackJson || path.join(outputDir, 'context-pack.import.json'),
    execPlanJson: options.execPlanJson || path.join(outputDir, 'exec-plan.v2.json'),
  };
}

function renderHelp() {
  return [
    'Spec Kit feature importer for ae-framework Context Pack and ExecPlan v2 bridge artifacts',
    '',
    'Usage:',
    `  node ${SCRIPT_NAME} [options]`,
    '',
    'Options:',
    `  --feature-dir <path>         Spec Kit feature directory (default: ${DEFAULT_FEATURE_DIR})`,
    '  --project-root, --work <path> repository root used for relative paths (default: .)',
    `  --output-dir <path>          output directory (default: ${DEFAULT_OUTPUT_DIR})`,
    '  --report-json <path>         bridge report JSON output path',
    '  --report-md <path>           bridge report Markdown output path',
    '  --context-pack-json <path>   generated Context Pack fixture output path',
    '  --exec-plan-json <path>      generated ExecPlan v2 fixture output path',
    '  --generated-at <iso-date>    deterministic timestamp for fixtures/tests',
    '  --source-issue <id>          source Issue id or URL for ExecPlan metadata (default: #3550)',
    '  --repo <owner/name>          repository name for ExecPlan metadata (default: itdojp/ae-framework)',
    '  --no-write                  validate/render in memory without writing outputs',
    '  --help                      show this help',
  ].join('\n');
}

function readOptionalFile(filePath, kind, rootDir) {
  const resolved = path.resolve(filePath);
  if (!existsSync(resolved) || !statSync(resolved).isFile()) {
    return {
      kind,
      path: normalizePathForReport(resolved, rootDir),
      present: false,
      bytes: 0,
      sha256: null,
      content: '',
    };
  }
  const content = readFileSync(resolved, 'utf8');
  return {
    kind,
    path: normalizePathForReport(resolved, rootDir),
    present: true,
    bytes: Buffer.byteLength(content),
    sha256: sha256(content),
    content,
  };
}

function listFilesRecursive(dirPath) {
  const resolved = path.resolve(dirPath);
  if (!existsSync(resolved) || !statSync(resolved).isDirectory()) return [];
  const entries = [];
  for (const name of readdirSync(resolved).sort()) {
    if (name.startsWith('.')) continue;
    const child = path.join(resolved, name);
    const stat = statSync(child);
    if (stat.isDirectory()) {
      entries.push(...listFilesRecursive(child));
    } else if (stat.isFile()) {
      entries.push(child);
    }
  }
  return entries;
}


function findConstitutionPath(featureDir, projectRoot) {
  const root = path.resolve(projectRoot);
  let cursor = path.resolve(featureDir);
  while (true) {
    const candidate = path.join(cursor, '.specify', 'memory', 'constitution.md');
    if (existsSync(candidate) && statSync(candidate).isFile()) return candidate;
    if (cursor === root) break;
    const parent = path.dirname(cursor);
    if (parent === cursor) break;
    if (!path.relative(root, parent).startsWith('..') || parent === root) {
      cursor = parent;
      continue;
    }
    break;
  }
  return path.join(root, '.specify', 'memory', 'constitution.md');
}

function readContracts(contractsDir, rootDir) {
  return listFilesRecursive(contractsDir).map((filePath) => {
    const input = readOptionalFile(filePath, 'contract', rootDir);
    return {
      ...input,
      contractKind: classifyContract(input.path, input.content),
    };
  });
}

function classifyContract(filePath, content) {
  const extension = path.extname(filePath).toLowerCase();
  if (/openapi\s*:/i.test(content)) return 'openapi';
  if (extension === '.json') return 'json';
  if (extension === '.yaml' || extension === '.yml') return 'yaml';
  if (extension === '.md' || extension === '.markdown') return 'markdown';
  return 'other';
}

function sectionBody(markdown, headingPattern, level = null) {
  const lines = String(markdown || '').split(/\r?\n/);
  const startIndex = lines.findIndex((line) => {
    const match = /^(#{1,6})\s+(.+?)\s*$/.exec(line);
    if (!match) return false;
    if (level && match[1].length !== level) return false;
    return headingPattern.test(stripMarkdown(match[2]));
  });
  if (startIndex === -1) return '';
  const startHeading = /^(#{1,6})\s+/.exec(lines[startIndex])?.[1].length || 2;
  const body = [];
  for (let index = startIndex + 1; index < lines.length; index += 1) {
    const match = /^(#{1,6})\s+/.exec(lines[index]);
    if (match && match[1].length <= startHeading) break;
    body.push(lines[index]);
  }
  return body.join('\n').trim();
}

function bullets(markdown) {
  return String(markdown || '')
    .split(/\r?\n/)
    .map((line) => /^\s*(?:[-*]|\d+[.)])\s+(.*)$/.exec(line)?.[1])
    .filter(Boolean)
    .map(normalizeLine)
    .filter(Boolean);
}

function firstHeading(markdown) {
  const match = /^#\s+(.+?)\s*$/m.exec(String(markdown || ''));
  return match ? normalizeLine(match[1]) : '';
}

function parseFeatureName(specContent, featureDir) {
  const heading = firstHeading(specContent);
  const fromHeading = /^Feature Specification:\s*(.+)$/i.exec(heading)?.[1];
  if (fromHeading && !/\[feature name\]/i.test(fromHeading)) return normalizeLine(fromHeading);
  const summary = sectionBody(specContent, /^Summary$/i);
  if (summary) return normalizeLine(summary.split(/\r?\n/).find((line) => line.trim()) || '');
  return titleFromSlug(path.basename(featureDir));
}

function parseField(content, label) {
  const pattern = new RegExp(`^\\*\\*${label.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\*\\*\\s*:\\s*(.+)$`, 'im');
  return normalizeLine(pattern.exec(content)?.[1] || '');
}

function parseRequirements(specContent) {
  const section = sectionBody(specContent, /^Functional Requirements/i) || sectionBody(specContent, /^Requirements/i);
  const requirements = [];
  const seen = new Set();
  for (const line of String(section || '').split(/\r?\n/)) {
    const match = /^\s*[-*]\s+(?:\*\*)?([A-Z]{2,}-\d{3})(?:\*\*)?\s*:?\s*(.+)$/.exec(line);
    if (!match) continue;
    const id = match[1];
    const text = normalizeLine(match[2]);
    if (!seen.has(id) && text) {
      seen.add(id);
      requirements.push({ id, text });
    }
  }
  if (requirements.length === 0) {
    bullets(section).slice(0, 12).forEach((text, index) => {
      requirements.push({ id: `FR-${String(index + 1).padStart(3, '0')}`, text });
    });
  }
  return requirements;
}

function parseUserStories(specContent) {
  const lines = String(specContent || '').split(/\r?\n/);
  const stories = [];
  for (let index = 0; index < lines.length; index += 1) {
    const match = /^###\s+User Story\s+(\d+)\s*-\s*(.+?)(?:\s*\(([^)]+)\))?\s*$/.exec(lines[index]);
    if (!match) continue;
    const body = [];
    for (let cursor = index + 1; cursor < lines.length; cursor += 1) {
      if (/^###\s+User Story\s+\d+\s*-/.test(lines[cursor]) || /^##\s+/.test(lines[cursor])) break;
      body.push(lines[cursor]);
    }
    const bodyText = body.join('\n');
    const priority = /P\d/i.exec(match[3] || '')?.[0]?.toUpperCase() || 'P?';
    const acceptanceSection = sectionBody(bodyText, /^Acceptance Scenarios/i) || bodyText;
    stories.push({
      id: `US${match[1]}`,
      title: normalizeLine(match[2]),
      priority,
      independentTest: normalizeLine(/^\*\*Independent Test\*\*\s*:\s*(.+)$/im.exec(bodyText)?.[1] || ''),
      acceptanceScenarios: bullets(acceptanceSection).slice(0, 8),
    });
  }
  return stories;
}

function parseSuccessCriteria(specContent) {
  const section = sectionBody(specContent, /^Measurable Outcomes/i) || sectionBody(specContent, /^Success Criteria/i);
  return bullets(section).slice(0, 12).map((text, index) => ({
    id: `SC-${String(index + 1).padStart(3, '0')}`,
    text,
  }));
}

function parsePlan(planContent) {
  const technicalContext = sectionBody(planContent, /^Technical Context/i);
  const fields = {};
  for (const line of technicalContext.split(/\r?\n/)) {
    const match = /^\s*\*\*([^*]+)\*\*\s*:\s*(.+)$/.exec(line);
    if (match) fields[normalizeLine(match[1])] = normalizeLine(match[2]);
  }
  return {
    title: normalizeLine(/^#\s+Implementation Plan:\s*(.+)$/im.exec(planContent)?.[1] || ''),
    branch: parseField(planContent, 'Branch'),
    specLink: normalizeLine(/\|\s*\*\*Spec\*\*:\s*([^|]+)$/im.exec(planContent)?.[1] || ''),
    summary: normalizeLine(sectionBody(planContent, /^Summary/i).split(/\r?\n/).find((line) => line.trim()) || ''),
    technicalContext: fields,
    constitutionCheck: bullets(sectionBody(planContent, /^Constitution Check/i)).slice(0, 10),
  };
}

function parseTasks(tasksContent) {
  const lines = String(tasksContent || '').split(/\r?\n/);
  const tasks = [];
  let phase = 'Unspecified';
  for (const line of lines) {
    const phaseMatch = /^##\s+(Phase\s+\S+\s*:\s*.+|.+)$/.exec(line);
    if (phaseMatch) {
      phase = normalizeLine(phaseMatch[1]);
      continue;
    }
    const match = /^\s*-\s+\[[ xX]\]\s+(T\d{3})\s*(.*)$/.exec(line);
    if (!match) continue;
    const tail = match[2].trim();
    const markers = [...tail.matchAll(/\[([^\]]+)\]/g)].map((item) => item[1]);
    const storyRef = markers.find((marker) => /^US\d+$/i.test(marker))?.toUpperCase() || null;
    const parallel = markers.some((marker) => marker.toUpperCase() === 'P');
    const title = normalizeLine(tail.replace(/\[[^\]]+\]/g, ''));
    tasks.push({
      id: match[1],
      title: title || match[1],
      phase,
      storyRef,
      parallel,
      sourceLine: normalizeLine(line),
    });
  }
  return tasks;
}

function buildInputDescriptor(input, extra = {}) {
  const { content: _content, ...publicInput } = input;
  return { ...publicInput, ...extra };
}

function makeSourceRef(kind, id, pathValue, description) {
  const ref = { kind, id };
  if (pathValue) ref.path = pathValue;
  if (description) ref.description = description;
  return ref;
}

function buildAnalysis(options) {
  const projectRoot = path.resolve(options.projectRoot);
  const featureDir = path.resolve(projectRoot, options.featureDir);
  const featureRelativePath = normalizePathForReport(featureDir, projectRoot);
  const featureId = slugify(path.basename(featureDir));
  const generatedAt = options.generatedAt || new Date().toISOString();
  const sourceIssueRef = options.sourceIssue.startsWith('http')
    ? { kind: 'issue', id: options.sourceIssue.split('/').pop() || options.sourceIssue, url: options.sourceIssue, description: 'Source Issue for Spec Kit bridge work.' }
    : { kind: 'issue', id: options.sourceIssue, url: `https://github.com/${options.repository}/issues/${String(options.sourceIssue).replace(/^#/, '')}`, description: 'Source Issue for Spec Kit bridge work.' };

  if (!existsSync(featureDir) || !statSync(featureDir).isDirectory()) {
    const report = {
      schemaVersion: 'spec-kit-bridge-report/v1',
      contractId: 'spec-kit-bridge-report',
      generatedAt,
      result: FAIL,
      source: {
        repository: options.repository,
        featureId,
        featureName: titleFromSlug(featureId),
        projectRoot: normalizePathForReport(projectRoot, projectRoot),
        featureDir: featureRelativePath,
        upstream: SPEC_KIT_UPSTREAM,
      },
      inputs: [],
      outputs: [],
      summary: {
        requirements: 0,
        userStories: 0,
        tasks: 0,
        contracts: 0,
        findings: 1,
        ambiguousMappings: 0,
        lossyMappings: 0,
      },
      mappings: [],
      unsupportedFields: [],
      findings: [{ severity: 'error', code: 'missing-feature-dir', message: `Feature directory not found: ${featureRelativePath}`, sourcePath: featureRelativePath }],
    };
    return { report, contextPack: null, execPlan: null, markdown: renderReportMarkdown(report), options: { ...options, projectRoot } };
  }

  const spec = readOptionalFile(path.join(featureDir, 'spec.md'), 'spec', projectRoot);
  const plan = readOptionalFile(path.join(featureDir, 'plan.md'), 'plan', projectRoot);
  const tasksInput = readOptionalFile(path.join(featureDir, 'tasks.md'), 'tasks', projectRoot);
  const research = readOptionalFile(path.join(featureDir, 'research.md'), 'research', projectRoot);
  const dataModel = readOptionalFile(path.join(featureDir, 'data-model.md'), 'data-model', projectRoot);
  const quickstart = readOptionalFile(path.join(featureDir, 'quickstart.md'), 'quickstart', projectRoot);
  const constitution = readOptionalFile(findConstitutionPath(featureDir, projectRoot), 'constitution', projectRoot);
  const contracts = readContracts(path.join(featureDir, 'contracts'), projectRoot);

  const featureName = parseFeatureName(spec.content, featureDir);
  const requirements = parseRequirements(spec.content);
  const userStories = parseUserStories(spec.content);
  const successCriteria = parseSuccessCriteria(spec.content);
  const planInfo = parsePlan(plan.content);
  const tasks = parseTasks(tasksInput.content);
  const featurePascal = pascalCase(featureName || featureId);
  const findings = [];
  const unsupportedFields = [];
  const mappings = [];

  for (const requiredInput of [spec, plan, tasksInput]) {
    if (!requiredInput.present) {
      findings.push({
        severity: 'warning',
        code: `missing-${requiredInput.kind}`,
        message: `${requiredInput.kind}.md was not found; bridge output records the gap and remains report-only.`,
        sourcePath: requiredInput.path,
      });
    }
  }
  if (!constitution.present) {
    findings.push({
      severity: 'warning',
      code: 'missing-constitution',
      message: 'Spec Kit constitution was not found; governance constraints cannot be mapped into Context Pack forbidden_changes.',
      sourcePath: constitution.path,
    });
  }
  if (contracts.length === 0) {
    findings.push({
      severity: 'warning',
      code: 'missing-contracts',
      message: 'No contracts/* files were found; contract mappings are recorded as not_collected.',
      sourcePath: normalizePathForReport(path.join(featureDir, 'contracts'), projectRoot),
    });
  }
  if (requirements.length === 0) {
    findings.push({
      severity: 'warning',
      code: 'missing-requirements',
      message: 'No functional requirements were detected in spec.md.',
      sourcePath: spec.path,
    });
  }
  for (const task of tasks) {
    if (!task.storyRef && !/setup|foundation|polish|cross-cutting/i.test(task.phase)) {
      findings.push({
        severity: 'warning',
        code: 'ambiguous-task-story',
        message: `${task.id} has no [US#] marker; it is preserved as an ExecPlan task but cannot be linked to a specific user story.`,
        sourcePath: tasksInput.path,
      });
    }
  }
  for (const input of [spec, plan, tasksInput, constitution]) {
    if (input.present && /\[(?:NEEDS CLARIFICATION|FEATURE NAME|TODO|TBD)\]/i.test(input.content)) {
      findings.push({
        severity: 'warning',
        code: 'template-placeholder-detected',
        message: `${input.kind} contains unfilled Spec Kit template placeholders.`,
        sourcePath: input.path,
      });
    }
  }

  unsupportedFields.push(
    {
      sourceKind: 'spec-kit-command',
      field: 'agent hooks and invocation side effects',
      sourcePath: '.specify/templates/commands/*.md',
      reason: 'ae-framework bridge records artifact references but does not execute Spec Kit commands, agent hooks, or task-to-issues side effects.',
      disposition: 'report-only-lossy',
    },
    {
      sourceKind: 'tasks',
      field: 'free-form task prose ordering',
      sourcePath: tasksInput.path,
      reason: 'Tasks are mapped to ExecPlan nodes and Context Pack references; nuanced prose ordering remains in the source task line.',
      disposition: 'preserved-as-source-reference',
    },
  );

  for (const requirement of requirements) {
    mappings.push({
      sourceKind: 'spec.requirement',
      sourceId: requirement.id,
      sourcePath: spec.path,
      targetKind: 'context-pack.acceptance-test',
      targetId: `AT-${requirement.id}`,
      confidence: 'high',
      lossy: false,
      notes: ['Functional requirements become acceptance-test anchors for assurance review.'],
    });
  }
  for (const story of userStories) {
    mappings.push({
      sourceKind: 'spec.user-story',
      sourceId: story.id,
      sourcePath: spec.path,
      targetKind: 'context-pack.morphism',
      targetId: `${featurePascal}.${story.id}`,
      confidence: 'medium',
      lossy: story.acceptanceScenarios.length === 0,
      notes: story.acceptanceScenarios.length > 0
        ? ['Acceptance scenarios are preserved in Context Pack acceptance tests.']
        : ['No explicit acceptance scenarios were detected.'],
    });
  }
  for (const task of tasks) {
    mappings.push({
      sourceKind: 'tasks.task',
      sourceId: task.id,
      sourcePath: tasksInput.path,
      targetKind: 'exec-plan.taskGraph.node',
      targetId: `task.${task.id.toLowerCase()}`,
      confidence: task.storyRef ? 'high' : 'medium',
      lossy: !task.storyRef,
      notes: [task.storyRef ? `Linked to ${task.storyRef}.` : 'No user-story marker; phase and source line are preserved.'],
    });
  }
  for (const contract of contracts) {
    mappings.push({
      sourceKind: 'contracts.file',
      sourceId: path.basename(contract.path),
      sourcePath: contract.path,
      targetKind: 'exec-plan.context.specKitRefs',
      targetId: `contract.${slugify(path.basename(contract.path, path.extname(contract.path)))}`,
      confidence: 'high',
      lossy: false,
      notes: [`Contract kind detected as ${contract.contractKind}.`],
    });
  }

  const normalizedOutputPaths = {
    reportJson: normalizePathForReport(path.resolve(projectRoot, options.reportJson), projectRoot),
    contextPackJson: normalizePathForReport(path.resolve(projectRoot, options.contextPackJson), projectRoot),
    execPlanJson: normalizePathForReport(path.resolve(projectRoot, options.execPlanJson), projectRoot),
  };

  const contextPack = buildContextPack({
    featureId,
    featureName,
    featurePascal,
    featureRelativePath,
    spec,
    plan,
    tasksInput,
    constitution,
    contracts,
    requirements,
    userStories,
    successCriteria,
    planInfo,
    tasks,
    findings,
    outputPaths: normalizedOutputPaths,
  });
  const execPlan = buildExecPlan({
    featureId,
    featureName,
    featureRelativePath,
    spec,
    plan,
    tasksInput,
    constitution,
    contracts,
    requirements,
    userStories,
    planInfo,
    tasks,
    findings,
    sourceIssueRef,
    options,
    generatedAt,
    outputPaths: normalizedOutputPaths,
  });

  const outputArtifacts = [
    { kind: 'bridge-report', path: normalizedOutputPaths.reportJson, schemaPath: 'schema/spec-kit-bridge-report.schema.json' },
    { kind: 'context-pack', path: normalizedOutputPaths.contextPackJson, schemaPath: 'schema/context-pack-v1.schema.json' },
    { kind: 'exec-plan', path: normalizedOutputPaths.execPlanJson, schemaPath: 'schema/exec-plan.v2.schema.json' },
  ];

  const report = {
    schemaVersion: 'spec-kit-bridge-report/v1',
    contractId: 'spec-kit-bridge-report',
    generatedAt,
    result: findings.some((finding) => finding.severity === 'error') ? FAIL : findings.length > 0 ? WARNING : PASS,
    source: {
      repository: options.repository,
      featureId,
      featureName,
      projectRoot: normalizePathForReport(projectRoot, projectRoot),
      featureDir: featureRelativePath,
      upstream: SPEC_KIT_UPSTREAM,
    },
    inputs: [
      buildInputDescriptor(constitution),
      buildInputDescriptor(spec),
      buildInputDescriptor(plan),
      buildInputDescriptor(tasksInput),
      ...(research.present ? [buildInputDescriptor(research)] : []),
      ...(dataModel.present ? [buildInputDescriptor(dataModel)] : []),
      ...(quickstart.present ? [buildInputDescriptor(quickstart)] : []),
      ...contracts.map((contract) => buildInputDescriptor(contract, { contractKind: contract.contractKind })),
    ],
    outputs: outputArtifacts,
    summary: {
      requirements: requirements.length,
      userStories: userStories.length,
      tasks: tasks.length,
      contracts: contracts.length,
      findings: findings.length,
      ambiguousMappings: mappings.filter((mapping) => mapping.confidence !== 'high').length,
      lossyMappings: mappings.filter((mapping) => mapping.lossy).length + unsupportedFields.length,
    },
    mappings,
    unsupportedFields,
    findings,
  };

  return { report, contextPack, execPlan, markdown: renderReportMarkdown(report), options: { ...options, projectRoot } };
}

function buildContextPack(input) {
  const {
    featureId,
    featureName,
    featurePascal,
    featureRelativePath,
    spec,
    plan,
    tasksInput,
    constitution,
    contracts,
    requirements,
    userStories,
    successCriteria,
    planInfo,
    tasks,
    findings,
    outputPaths,
  } = input;

  const requirementGoals = requirements.map((requirement) => `${requirement.id}: ${requirement.text}`);
  const storyGoals = userStories.map((story) => `${story.id}: ${story.title}`);
  const language = planInfo.technicalContext['Language/Version'] || 'not_collected';
  const testing = planInfo.technicalContext.Testing || 'not_collected';
  const directories = (planInfo.technicalContext['Project Type'] || '')
    .split(/[,;]/)
    .map((item) => item.trim())
    .filter(Boolean);

  const acceptanceTests = [];
  for (const requirement of requirements) {
    acceptanceTests.push({
      id: `AT-${requirement.id}`,
      scenario: requirement.text,
      expected: successCriteria.length > 0 ? successCriteria.map((criterion) => criterion.text) : ['Implementation satisfies the mapped Spec Kit requirement.'],
      sourceRefs: [requirement.id],
    });
  }
  for (const story of userStories) {
    acceptanceTests.push({
      id: `AT-${story.id}`,
      scenario: `${story.title} (${story.priority})`,
      expected: story.acceptanceScenarios.length > 0 ? story.acceptanceScenarios : [story.independentTest || 'Story can be verified independently.'],
      sourceRefs: [story.id],
    });
  }
  if (acceptanceTests.length === 0) {
    acceptanceTests.push({
      id: 'AT-SPECKIT-IMPORT',
      scenario: 'Spec Kit feature imports without a detected requirement section.',
      expected: ['Bridge report records missing requirement mappings as report-only findings.'],
    });
  }

  return {
    version: 1,
    name: `spec-kit-${featureId}-context-pack`,
    problem_statement: {
      goals: requirementGoals.length > 0 ? requirementGoals : storyGoals.length > 0 ? storyGoals : [`Import Spec Kit feature ${featureName} into ae-framework assurance review inputs.`],
      non_goals: [
        'Do not vendor or fork GitHub Spec Kit.',
        'Do not require Spec Kit for normal ae-framework usage.',
        'Do not treat report-only bridge findings as merge approval.',
      ],
    },
    domain_glossary: {
      terms: [
        { term: slugify(featureName), ja: 'Spec Kit 取込フィーチャ', note: `Imported from ${featureRelativePath}` },
        { term: 'spec-kit-bridge', ja: 'Spec Kit 連携ブリッジ', note: 'Report-only mapping into Context Pack and ExecPlan v2 references.' },
      ],
    },
    objects: [
      {
        id: `SpecKitFeature.${featurePascal}`,
        kind: 'feature',
        sourcePath: spec.path,
        fields: ['spec.md', 'plan.md', 'tasks.md', 'contracts/*'],
      },
      ...contracts.map((contract) => ({
        id: `SpecKitContract.${pascalCase(path.basename(contract.path, path.extname(contract.path)))}`,
        kind: contract.contractKind,
        sourcePath: contract.path,
      })),
    ],
    morphisms: [
      {
        id: `Import${featurePascal}`,
        input: {
          spec: spec.path,
          plan: plan.path,
          tasks: tasksInput.path,
          constitution: constitution.path,
        },
        output: {
          contextPack: outputPaths?.contextPackJson || 'artifacts/spec-kit/context-pack.import.json',
          execPlan: outputPaths?.execPlanJson || 'artifacts/spec-kit/exec-plan.v2.json',
          bridgeReport: outputPaths?.reportJson || 'artifacts/spec-kit/spec-kit-bridge-report.json',
        },
        pre: ['Spec Kit feature directory is readable.'],
        post: ['Requirement, plan, task, contract, and verification references are preserved as report-only assurance inputs.'],
        failures: findings.length > 0 ? findings.map((finding) => finding.code) : ['BridgeMappingGap'],
        sourceRefs: requirements.map((requirement) => requirement.id),
      },
      ...userStories.map((story) => ({
        id: `${featurePascal}.${story.id}`,
        input: { story: story.id, spec: spec.path },
        output: { acceptanceTest: `AT-${story.id}` },
        pre: [story.independentTest || 'Story has a reviewable scenario.'],
        post: story.acceptanceScenarios.length > 0 ? story.acceptanceScenarios : ['Story remains traceable to tasks and acceptance review.'],
        failures: ['StoryMappingAmbiguous'],
        sourceRefs: [story.id],
      })),
    ],
    diagrams: [
      {
        id: 'D-SPECKIT-BRIDGE-1',
        statement: 'Spec Kit spec.md, plan.md, tasks.md, and contracts/* are imported into Context Pack and ExecPlan v2 without replacing their source artifacts.',
        verification: ['spec-kit-bridge-report', 'exec-plan:v2:validate', 'context-pack:validate'],
      },
    ],
    constraints: {
      sourceSystem: 'github/spec-kit',
      sourceFeatureDir: featureRelativePath,
      optionalIntegration: true,
      reportOnly: true,
      bridgeFindings: findings.map((finding) => finding.code),
      taskCount: tasks.length,
    },
    acceptance_tests: acceptanceTests,
    coding_conventions: {
      language,
      testing,
      directory: directories.length > 0 ? directories : ['not_collected'],
      dependencies: {
        runtime: (planInfo.technicalContext['Primary Dependencies'] || 'not_collected').split(/[,;]/).map((item) => item.trim()).filter(Boolean),
      },
    },
    forbidden_changes: [
      'Do not vendor or fork GitHub Spec Kit inside ae-framework.',
      'Do not promote bridge findings from report-only to blocking without a separate policy issue.',
      'Do not drop source Spec Kit artifact paths when rendering assurance evidence.',
    ],
  };
}

function buildExecPlan(input) {
  const {
    featureId,
    featureName,
    featureRelativePath,
    spec,
    plan,
    tasksInput,
    constitution,
    contracts,
    requirements,
    userStories,
    planInfo,
    tasks,
    findings,
    sourceIssueRef,
    options,
    generatedAt,
    outputPaths,
  } = input;
  const selectedTasks = tasks.slice(0, 24);
  const evidenceIds = [
    'ev.spec-kit-bridge-report',
    'ev.context-pack-import',
    'ev.exec-plan-v2-import',
  ];
  const outputArtifacts = [
    {
      id: 'artifact.spec-kit-bridge-report',
      path: outputPaths.reportJson,
      contractId: 'spec-kit-bridge-report',
      schemaPath: 'schema/spec-kit-bridge-report.schema.json',
      description: 'Report-only mapping from Spec Kit sources to ae-framework contracts.',
      producer: SCRIPT_NAME,
      requiredBefore: 'pr-review',
    },
    {
      id: 'artifact.context-pack-import',
      path: outputPaths.contextPackJson,
      contractId: 'context-pack-v1',
      schemaPath: 'schema/context-pack-v1.schema.json',
      description: 'Generated Context Pack fixture preserving Spec Kit requirement and task references.',
      producer: SCRIPT_NAME,
      requiredBefore: 'pr-review',
    },
    {
      id: 'artifact.exec-plan-v2-import',
      path: outputPaths.execPlanJson,
      contractId: 'exec-plan.v2',
      schemaPath: 'schema/exec-plan.v2.schema.json',
      description: 'Generated ExecPlan v2 fixture for the imported Spec Kit feature.',
      producer: SCRIPT_NAME,
      requiredBefore: 'pr-review',
    },
  ];
  return {
    schemaVersion: 'exec-plan/v2',
    contractId: 'exec-plan.v2',
    planId: `spec-kit-${featureId}-bridge`,
    title: `Spec Kit bridge import for ${featureName}`,
    lifecycle: 'preview',
    intent: {
      summary: `Import Spec Kit feature ${featureName} into ae-framework assurance review inputs.`,
      objective: 'Preserve requirement, plan, task, contract, and verification references in Context Pack and ExecPlan v2 without requiring Spec Kit for normal ae-framework usage.',
      sourceReferences: [
        sourceIssueRef,
        makeSourceRef('spec-kit', featureId, featureRelativePath, 'Spec Kit feature directory.'),
        makeSourceRef('document', 'spec-kit-upstream', null, 'GitHub Spec Kit upstream workflow and templates.'),
      ],
      nonGoals: [
        'Do not vendor or fork GitHub Spec Kit.',
        'Do not execute Spec Kit agent commands or task-to-issues side effects.',
        'Do not make bridge findings blocking in this preview issue.',
      ],
    },
    scope: {
      inScope: [
        'Read Spec Kit feature artifacts and emit ae-framework-compatible report-only artifacts.',
        'Map requirements, plans, tasks, contracts, and verification references into Context Pack and ExecPlan v2 surfaces.',
      ],
      outOfScope: [
        'Hosted orchestrator implementation.',
        'Spec Kit command execution or GitHub Issue creation.',
        'Policy-gate enforcement changes.',
      ],
      targetFiles: [spec, plan, tasksInput, constitution, ...contracts].map((input) => ({
        path: input.path,
        changeType: 'read-only',
        reason: `${input.kind} source consumed by the bridge importer.`,
      })),
      affectedContracts: [
        {
          contractId: 'spec-kit-bridge-report',
          schemaPath: 'schema/spec-kit-bridge-report.schema.json',
          lifecycle: 'preview',
          reason: 'New report-only bridge artifact emitted by the importer.',
        },
        {
          contractId: 'context-pack-v1',
          schemaPath: 'schema/context-pack-v1.schema.json',
          lifecycle: 'stable',
          reason: 'Bridge emits a fixture-compatible Context Pack import artifact.',
        },
        {
          contractId: 'exec-plan.v2',
          schemaPath: 'schema/exec-plan.v2.schema.json',
          lifecycle: 'preview',
          reason: 'Bridge emits a fixture-compatible ExecPlan v2 import artifact.',
        },
      ],
    },
    context: {
      contextPackRefs: [
        {
          kind: 'context-pack',
          refId: `spec-kit-${featureId}-context-pack`,
          path: outputPaths.contextPackJson,
          description: 'Generated Context Pack import artifact.',
        },
      ],
      assuranceRefs: {
        mode: 'report-only',
        profiles: [],
        claimRefs: requirements.map((requirement) => requirement.id),
        summaryArtifacts: ['artifacts/assurance/assurance-summary.json'],
      },
      specKitRefs: [
        { kind: 'spec-kit-spec', refId: `${featureId}.spec`, path: spec.path, description: 'Spec Kit feature specification.' },
        { kind: 'spec-kit-plan', refId: `${featureId}.plan`, path: plan.path, description: 'Spec Kit implementation plan.' },
        { kind: 'spec-kit-task', refId: `${featureId}.tasks`, path: tasksInput.path, description: 'Spec Kit generated task list.' },
        ...contracts.map((contract) => ({ kind: 'artifact-contract', refId: `contract.${slugify(path.basename(contract.path, path.extname(contract.path)))}`, path: contract.path, description: `Spec Kit contract artifact (${contract.contractKind}).` })),
      ],
    },
    taskGraph: {
      nodes: [
        {
          id: 'task.import-spec-kit',
          title: 'Import Spec Kit feature artifacts',
          kind: 'analysis',
          owner: 'agent',
          status: 'planned',
          dependsOn: [],
          evidenceRequirementRefs: ['ev.spec-kit-bridge-report'],
          commands: [
            {
              id: 'cmd.spec-kit-import',
              command: `pnpm run spec-kit:import-feature -- --feature-dir ${featureRelativePath} --output-dir artifacts/spec-kit`,
              purpose: 'Generate bridge report, Context Pack import, and ExecPlan v2 import artifacts.',
              when: 'local-validation',
              expectedArtifactRefs: ['artifact.spec-kit-bridge-report', 'artifact.context-pack-import', 'artifact.exec-plan-v2-import'],
            },
          ],
          outputArtifactRefs: ['artifact.spec-kit-bridge-report', 'artifact.context-pack-import', 'artifact.exec-plan-v2-import'],
        },
        ...selectedTasks.map((task, index) => ({
          id: `task.${task.id.toLowerCase()}`,
          title: task.title,
          kind: /test|verify|validate|check/i.test(task.title) ? 'verification' : 'implementation',
          owner: 'either',
          status: 'planned',
          dependsOn: index === 0 ? ['task.import-spec-kit'] : [`task.${selectedTasks[index - 1].id.toLowerCase()}`],
          evidenceRequirementRefs: evidenceIds,
          commands: [],
          outputArtifactRefs: ['artifact.spec-kit-bridge-report'],
        })),
      ],
    },
    verificationProfile: {
      mode: findings.length > 0 ? 'structured-assurance' : 'fast-lane',
      commands: [
        {
          id: 'cmd.spec-kit-import',
          command: `pnpm run spec-kit:import-feature -- --feature-dir ${featureRelativePath} --output-dir artifacts/spec-kit`,
          purpose: 'Regenerate bridge artifacts and report missing or ambiguous mappings.',
          when: 'local-validation',
          expectedArtifactRefs: ['artifact.spec-kit-bridge-report', 'artifact.context-pack-import', 'artifact.exec-plan-v2-import'],
        },
        {
          id: 'cmd.exec-plan-v2-validate',
          command: `pnpm run exec-plan:v2:validate -- --file ${options.execPlanJson}`,
          purpose: 'Validate generated ExecPlan v2 artifact.',
          when: 'pre-merge',
          expectedArtifactRefs: ['artifact.exec-plan-v2-import'],
        },
        {
          id: 'cmd.schema-validation',
          command: 'node scripts/ci/validate-json.mjs',
          purpose: 'Validate bridge report, Context Pack import, and ExecPlan v2 fixture schemas.',
          when: 'pre-merge',
          expectedArtifactRefs: ['artifact.spec-kit-bridge-report', 'artifact.context-pack-import', 'artifact.exec-plan-v2-import'],
        },
      ],
      requiredChecks: ['verify-lite', 'policy-gate'],
      optionalChecks: ['gate'],
    },
    evidenceRequirements: [
      {
        id: 'ev.spec-kit-bridge-report',
        kind: 'other',
        description: 'Bridge report records detected mappings, unsupported fields, and missing/ambiguous references.',
        requiredBefore: 'pr-review',
        producer: SCRIPT_NAME,
        sourceRefs: [makeSourceRef('spec-kit', featureId, featureRelativePath, 'Spec Kit feature directory.')],
        outputArtifactRefs: ['artifact.spec-kit-bridge-report'],
      },
      {
        id: 'ev.context-pack-import',
        kind: 'context-pack',
        description: 'Generated Context Pack import artifact is schema-compatible and keeps Spec Kit source paths.',
        requiredBefore: 'pr-review',
        producer: SCRIPT_NAME,
        outputArtifactRefs: ['artifact.context-pack-import'],
      },
      {
        id: 'ev.exec-plan-v2-import',
        kind: 'exec-plan',
        description: 'Generated ExecPlan v2 artifact is schema-compatible and records validation commands.',
        requiredBefore: 'merge-judgment',
        producer: SCRIPT_NAME,
        outputArtifactRefs: ['artifact.exec-plan-v2-import'],
      },
    ],
    riskProfile: {
      selected: 'risk:low',
      rationale: 'The bridge is optional and report-only; it reads local Spec Kit artifacts and emits review artifacts without changing policy enforcement.',
      requiresHumanApproval: false,
      minHumanApprovals: 0,
      assuranceDecision: 'report-only',
      policyRefs: [
        { kind: 'policy-rule', refId: 'risk-policy', path: 'policy/risk-policy.yml', description: 'Repository risk label and policy-gate rules remain authoritative.' },
      ],
    },
    allowedActions: {
      automation: ['read-repository', 'generate-artifact', 'run-local-command'],
      humanApprovalRequiredFor: ['merge-pr', 'publish-release'],
      forbidden: [],
    },
    stopRules: [
      {
        id: 'stop.missing-feature-dir',
        severity: 'blocker',
        condition: 'The selected Spec Kit feature directory cannot be read.',
        action: 'halt-and-record-blocker',
        evidenceRequirementRefs: ['ev.spec-kit-bridge-report'],
      },
      {
        id: 'stop.policy-promotion',
        severity: 'warning',
        condition: 'A bridge finding is proposed as a blocking policy condition in this preview issue.',
        action: 'halt-and-ask-human',
        evidenceRequirementRefs: ['ev.spec-kit-bridge-report'],
      },
    ],
    rollbackPlan: {
      strategy: 'Remove generated bridge artifacts and importer wiring; source Spec Kit artifacts remain unchanged.',
      steps: [
        'Delete generated artifacts under artifacts/spec-kit/ if created locally.',
        'Remove spec-kit bridge report schema registration and docs links in a follow-up revert if needed.',
        'Keep upstream Spec Kit source directories untouched.',
      ],
      validationCommands: [
        {
          id: 'cmd.rollback-validate-json',
          command: 'node scripts/ci/validate-json.mjs',
          purpose: 'Confirm schema registry remains valid after rollback.',
          when: 'manual-review',
          expectedArtifactRefs: ['artifact.spec-kit-bridge-report'],
        },
      ],
    },
    outputArtifacts,
    metadata: {
      createdAt: generatedAt,
      generator: SCRIPT_NAME,
      repository: options.repository,
      sourceIssue: sourceIssueRef,
      notes: [
        `Feature source: ${featureRelativePath}`,
        `Detected ${requirements.length} requirements, ${userStories.length} user stories, ${tasks.length} tasks, and ${contracts.length} contracts.`,
        planInfo.summary || 'Plan summary not collected.',
      ],
    },
  };
}

function renderReportMarkdown(report) {
  const lines = [
    `# Spec Kit Bridge Report: ${report.source.featureName}`,
    '',
    `- Result: \`${report.result}\``,
    `- Generated at: ${report.generatedAt}`,
    `- Feature directory: \`${report.source.featureDir}\``,
    `- Upstream: ${report.source.upstream.repository} (${report.source.upstream.reference})`,
    '',
    '## Summary',
    '',
    `- Requirements: ${report.summary.requirements}`,
    `- User stories: ${report.summary.userStories}`,
    `- Tasks: ${report.summary.tasks}`,
    `- Contracts: ${report.summary.contracts}`,
    `- Findings: ${report.summary.findings}`,
    `- Ambiguous mappings: ${report.summary.ambiguousMappings}`,
    `- Lossy mappings: ${report.summary.lossyMappings}`,
    '',
    '## Outputs',
    '',
    ...report.outputs.map((output) => `- ${output.kind}: \`${output.path}\` (${output.schemaPath})`),
    '',
    '## Findings',
    '',
  ];
  if (report.findings.length === 0) {
    lines.push('- None.');
  } else {
    for (const finding of report.findings) {
      lines.push(`- [${finding.severity}] ${finding.code}: ${finding.message} (${finding.sourcePath})`);
    }
  }
  lines.push('', '## Mapping highlights', '');
  if (report.mappings.length === 0) {
    lines.push('- No mappings detected.');
  } else {
    for (const mapping of report.mappings.slice(0, 20)) {
      lines.push(`- ${mapping.sourceKind} \`${mapping.sourceId}\` -> ${mapping.targetKind} \`${mapping.targetId}\` (${mapping.confidence}${mapping.lossy ? ', lossy' : ''})`);
    }
    if (report.mappings.length > 20) lines.push(`- ... ${report.mappings.length - 20} additional mappings omitted from Markdown summary.`);
  }
  lines.push('', '## Unsupported / lossy fields', '');
  for (const field of report.unsupportedFields) {
    lines.push(`- ${field.sourceKind} ${field.field}: ${field.reason} (${field.disposition})`);
  }
  return `${lines.join('\n')}\n`;
}

function writeJson(filePath, value) {
  mkdirSync(path.dirname(filePath), { recursive: true });
  writeFileSync(filePath, `${JSON.stringify(value, null, 2)}\n`, 'utf8');
}

function writeText(filePath, value) {
  mkdirSync(path.dirname(filePath), { recursive: true });
  writeFileSync(filePath, value, 'utf8');
}

function run(options = parseArgs()) {
  if (options.help) {
    process.stdout.write(`${renderHelp()}\n`);
    return { status: 0, report: null };
  }
  const result = buildAnalysis(options);
  if (!options.noWrite) {
    writeJson(path.resolve(result.options.projectRoot, options.reportJson), result.report);
    writeText(path.resolve(result.options.projectRoot, options.reportMd), result.markdown);
    if (result.contextPack) writeJson(path.resolve(result.options.projectRoot, options.contextPackJson), result.contextPack);
    if (result.execPlan) writeJson(path.resolve(result.options.projectRoot, options.execPlanJson), result.execPlan);
  }
  const statusLine = `[spec-kit:import-feature] ${result.report.result}: ${result.report.source.featureDir} -> ${options.reportJson}`;
  if (result.report.result === FAIL) {
    process.stderr.write(`${statusLine}\n`);
    return { status: 1, ...result };
  }
  process.stdout.write(`${statusLine}\n`);
  return { status: 0, ...result };
}

function isDirectExecution() {
  return Boolean(process.argv[1]) && import.meta.url === pathToFileURL(path.resolve(process.argv[1])).href;
}

if (isDirectExecution()) {
  try {
    const { status } = run(parseArgs(process.argv));
    process.exit(status);
  } catch (error) {
    process.stderr.write(`[spec-kit:import-feature] ${error.message}\n`);
    process.exit(1);
  }
}

export {
  buildAnalysis,
  buildContextPack,
  buildExecPlan,
  parseArgs,
  renderReportMarkdown,
  run
};
