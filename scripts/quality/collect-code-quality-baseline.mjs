#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { spawnSync } from 'node:child_process';
import { pathToFileURL } from 'node:url';

const SCHEMA_VERSION = 'quality-baseline/v1';
const CONTRACT_ID = 'quality-baseline.v1';
const DEFAULT_GENERATED_AT = '1970-01-01T00:00:00.000Z';
const DEFAULT_OUTPUT_JSON = 'artifacts/quality/code-quality-baseline.json';
const DEFAULT_OUTPUT_MD = 'artifacts/quality/code-quality-baseline.md';
const DEFAULT_DEBT_LEDGER = 'docs/quality/code-quality-debt-ledger.json';
const INVENTORY_SAMPLE_LIMIT = 20;
const PUBLIC_SCRIPT_NAMES = new Set([
  'ae-framework',
  'check:doc-consistency',
  'types:check',
  'test:fast',
  'lint',
  'lint:deps',
]);
const PUBLIC_SCRIPT_PREFIXES = [
  'quality:',
  'verify:',
  'context-pack:',
  'assurance:',
  'metrics:',
  'security:',
  'demo:',
];

function readRequiredValue(argv, index, option) {
  const value = argv[index + 1];
  if (!value || value.startsWith('--')) {
    throw new Error(`missing value for ${option}`);
  }
  return value;
}

export function parseArgs(argv = process.argv.slice(2)) {
  const options = {
    repoRoot: process.cwd(),
    outputJson: DEFAULT_OUTPUT_JSON,
    outputMd: DEFAULT_OUTPUT_MD,
    debtLedger: DEFAULT_DEBT_LEDGER,
    generatedAt: DEFAULT_GENERATED_AT,
    runChecks: false,
    help: false,
  };

  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--') {
      continue;
    }
    if (arg === '--repo-root') {
      options.repoRoot = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--output-json') {
      options.outputJson = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--output-md') {
      options.outputMd = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--debt-ledger') {
      options.debtLedger = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--generated-at') {
      options.generatedAt = readRequiredValue(argv, index, arg);
      index += 1;
      continue;
    }
    if (arg === '--run-checks') {
      options.runChecks = true;
      continue;
    }
    if (arg === '--help' || arg === '-h') {
      options.help = true;
      continue;
    }
    throw new Error(`unknown option: ${arg}`);
  }

  if (!Number.isNaN(Date.parse(options.generatedAt))) {
    options.generatedAt = new Date(options.generatedAt).toISOString();
  } else if (!options.help) {
    throw new Error(`--generated-at must be an ISO date-time: ${options.generatedAt}`);
  }

  return options;
}

function printHelp() {
  process.stdout.write(`Usage: node scripts/quality/collect-code-quality-baseline.mjs [options]\n\nOptions:\n  --repo-root <dir>       repository root (default: current working directory)\n  --output-json <path>    JSON output path (default: ${DEFAULT_OUTPUT_JSON})\n  --output-md <path>      Markdown output path (default: ${DEFAULT_OUTPUT_MD})\n  --debt-ledger <path>    quality debt ledger path (default: ${DEFAULT_DEBT_LEDGER})\n  --generated-at <iso>    artifact timestamp (default: ${DEFAULT_GENERATED_AT} for deterministic output)\n  --run-checks           execute configured local commands instead of reporting configured/missing status\n  --help                 show this help\n`);
}

function readJson(filePath) {
  return JSON.parse(fs.readFileSync(filePath, 'utf8'));
}

function toPosix(relativePath) {
  return relativePath.split(path.sep).join('/');
}

function resolveFromRoot(repoRoot, inputPath) {
  return path.isAbsolute(inputPath) ? inputPath : path.join(repoRoot, inputPath);
}

function relativeFromRoot(repoRoot, targetPath) {
  return toPosix(path.relative(repoRoot, targetPath));
}

function listFiles(repoRoot, relativeDir, extensions) {
  const absoluteDir = path.join(repoRoot, relativeDir);
  if (!fs.existsSync(absoluteDir)) {
    return [];
  }
  return fs.readdirSync(absoluteDir, { withFileTypes: true })
    .filter((entry) => entry.isFile() && extensions.some((extension) => entry.name.endsWith(extension)))
    .map((entry) => toPosix(path.join(relativeDir, entry.name)))
    .sort();
}

function createBucket(items) {
  return {
    count: items.length,
    sample: items.slice(0, INVENTORY_SAMPLE_LIMIT),
  };
}

function normalizeBinEntries(bin) {
  if (!bin) {
    return [];
  }
  if (typeof bin === 'string') {
    return [{ name: 'package-bin', path: bin }];
  }
  return Object.entries(bin)
    .map(([name, binPath]) => ({ name, path: String(binPath) }))
    .sort((left, right) => left.name.localeCompare(right.name));
}

function isPublicScript(name) {
  return PUBLIC_SCRIPT_NAMES.has(name) || PUBLIC_SCRIPT_PREFIXES.some((prefix) => name.startsWith(prefix));
}

function configuredStatus(scripts, scriptName, options) {
  if (!scripts[scriptName]) {
    return { status: 'missing', exitCode: null };
  }
  if (!options.runChecks) {
    return { status: 'configured', exitCode: null };
  }
  const command = `pnpm run ${scriptName}`;
  const result = spawnSync(command, {
    cwd: options.repoRoot,
    shell: true,
    stdio: 'ignore',
    timeout: 120_000,
  });
  return {
    status: result.status === 0 ? 'pass' : 'fail',
    exitCode: typeof result.status === 'number' ? result.status : 1,
  };
}

function fileCommandStatus(filePath, command, options) {
  if (!fs.existsSync(path.join(options.repoRoot, filePath))) {
    return { status: 'missing', exitCode: null };
  }
  if (!options.runChecks) {
    return { status: 'configured', exitCode: null };
  }
  const result = spawnSync(command, {
    cwd: options.repoRoot,
    shell: true,
    stdio: 'ignore',
    timeout: 120_000,
  });
  return {
    status: result.status === 0 ? 'pass' : 'fail',
    exitCode: typeof result.status === 'number' ? result.status : 1,
  };
}

function createQualityCheck(id, category, command, scriptName, scripts, options, rationale) {
  const status = configuredStatus(scripts, scriptName, options);
  return {
    id,
    category,
    command,
    status: status.status,
    reportOnly: true,
    rationale,
    exitCode: status.exitCode,
  };
}

function createFileQualityCheck(id, category, command, filePath, options, rationale) {
  const status = fileCommandStatus(filePath, command, options);
  return {
    id,
    category,
    command,
    status: status.status,
    reportOnly: true,
    rationale,
    exitCode: status.exitCode,
  };
}

function createDependencyBoundary(id, command, scriptName, scripts, options, scope, guardrail) {
  const status = configuredStatus(scripts, scriptName, options);
  return {
    id,
    command,
    status: status.status,
    reportOnly: true,
    scope,
    guardrail,
    exitCode: status.exitCode,
  };
}

function readDebtLedger(repoRoot, ledgerPath) {
  const resolvedLedger = resolveFromRoot(repoRoot, ledgerPath);
  if (!fs.existsSync(resolvedLedger)) {
    return { path: ledgerPath, items: [] };
  }
  const payload = readJson(resolvedLedger);
  const items = Array.isArray(payload.items) ? payload.items : [];
  return {
    path: relativeFromRoot(repoRoot, resolvedLedger),
    items: items.map((item) => ({
      id: String(item.id),
      owner: String(item.owner),
      reason: String(item.reason),
      reviewAfter: String(item.reviewAfter),
      targetCleanupSurface: String(item.targetCleanupSurface),
      source: String(item.source),
      links: Array.isArray(item.links) ? item.links.map(String) : [],
    })).sort((left, right) => left.id.localeCompare(right.id)),
  };
}

function createArchitecturePlanes() {
  return [
    {
      plane: 'Control',
      owner: 'architecture-maintainers',
      primaryPaths: ['docs/spec/context-pack.md', 'spec/context-pack/boundary-map.json', 'docs/reference/CONTRACT-CATALOG.md'],
      guardrails: [
        'Context Pack and boundary-map changes must be validated before implementation slices claim compatibility.',
        'New artifact contracts are cataloged before downstream producers consume them.',
      ],
    },
    {
      plane: 'Policy',
      owner: 'policy-maintainers',
      primaryPaths: ['policy/risk-policy.yml', 'scripts/ci/policy-gate.mjs', 'docs/ci-policy.md'],
      guardrails: [
        'Risk and enforcement decisions stay in policy-owned files, not ad hoc workflow branches.',
        'Report-only signals are promoted to blocking only after documented stability evidence.',
      ],
    },
    {
      plane: 'Execution',
      owner: 'runtime-maintainers',
      primaryPaths: ['package.json', 'scripts/ci/', 'scripts/quality/', '.github/workflows/'],
      guardrails: [
        'Local commands and CI workflows must share named package scripts where practical.',
        'Compatibility routes require explicit debt-ledger entries and review dates.',
      ],
    },
    {
      plane: 'Evidence',
      owner: 'evidence-maintainers',
      primaryPaths: ['schema/', 'fixtures/', 'artifacts/quality/'],
      guardrails: [
        'Machine-readable artifacts need schema coverage and fixture validation.',
        'Known exceptions are represented as data rather than hidden comments.',
      ],
    },
    {
      plane: 'Observability',
      owner: 'observability-maintainers',
      primaryPaths: ['docs/product/EFFECTIVENESS-METRICS.md', 'scripts/metrics/', 'artifacts/metrics/'],
      guardrails: [
        'Operational quality trends start as report-only metrics.',
        'Stop rules and escalation decisions reference observable evidence rather than reviewer memory.',
      ],
    },
  ];
}

function createTopCleanupCandidates(scriptWorkflowInventory, debtItems) {
  const candidates = debtItems.map((item) => ({
    id: item.id,
    category: 'debt-ledger',
    severity: 'medium',
    target: item.targetCleanupSurface,
    reason: item.reason,
  }));

  if (scriptWorkflowInventory.packageScripts.count >= 100) {
    candidates.push({
      id: 'package-script-sprawl',
      category: 'script-workflow-sprawl',
      severity: 'medium',
      target: 'package.json scripts',
      reason: `Package script inventory currently has ${scriptWorkflowInventory.packageScripts.count} entries; group or alias commands when adding new operational routes.`,
    });
  }

  if (scriptWorkflowInventory.githubWorkflows.count >= 30) {
    candidates.push({
      id: 'github-workflow-sprawl',
      category: 'script-workflow-sprawl',
      severity: 'medium',
      target: '.github/workflows',
      reason: `Workflow inventory currently has ${scriptWorkflowInventory.githubWorkflows.count} entries; prefer shared scripts and publisher patterns for new workflow behavior.`,
    });
  }

  return candidates.sort((left, right) => left.id.localeCompare(right.id));
}

function createFindings(qualityChecks, dependencyBoundaries, debtLedger, topCleanupCandidates) {
  const findings = [
    {
      id: 'report-only-baseline',
      severity: 'info',
      message: 'Code quality baseline is report-only and does not add a blocking PR gate.',
      reportOnly: true,
    },
    {
      id: 'debt-ledger-exceptions',
      severity: debtLedger.exceptionCount > 0 ? 'warn' : 'info',
      message: `Debt ledger contains ${debtLedger.exceptionCount} tracked exception(s).`,
      reportOnly: true,
    },
    {
      id: 'cleanup-candidate-count',
      severity: topCleanupCandidates.length > 0 ? 'warn' : 'info',
      message: `Baseline reports ${topCleanupCandidates.length} top cleanup candidate(s).`,
      reportOnly: true,
    },
  ];

  for (const check of [...qualityChecks, ...dependencyBoundaries]) {
    if (check.status === 'missing' || check.status === 'fail') {
      findings.push({
        id: `${check.id}-${check.status}`,
        severity: check.status === 'fail' ? 'error' : 'warn',
        message: `${check.command} status is ${check.status}.`,
        reportOnly: true,
      });
    }
  }

  return findings.sort((left, right) => left.id.localeCompare(right.id));
}

export function collectCodeQualityBaseline(options) {
  const repoRoot = path.resolve(options.repoRoot);
  const packageJsonPath = path.join(repoRoot, 'package.json');
  const packageJson = readJson(packageJsonPath);
  const scripts = packageJson.scripts ?? {};
  const scriptNames = Object.keys(scripts).sort();
  const qualityScripts = listFiles(repoRoot, 'scripts/quality', ['.mjs', '.js', '.ts']);
  const ciScripts = listFiles(repoRoot, 'scripts/ci', ['.mjs', '.js', '.ts']);
  const workflows = listFiles(repoRoot, '.github/workflows', ['.yml', '.yaml']);

  const qualityChecks = [
    createQualityCheck('types-check', 'type-safety', 'pnpm run types:check', 'types:check', scripts, options, 'TypeScript verification covers compile-time type safety for the configured verification tsconfig.'),
    createQualityCheck('lint', 'lint', 'pnpm run lint', 'lint', scripts, options, 'ESLint remains the primary local lint debt signal.'),
    createQualityCheck('test-fast', 'tests', 'pnpm run test:fast', 'test:fast', scripts, options, 'Fast tests are the ordinary PR regression baseline.'),
    createQualityCheck('doc-consistency', 'docs', 'pnpm -s run check:doc-consistency', 'check:doc-consistency', scripts, options, 'Documentation path, command, and contract consistency stays part of the quality baseline.'),
    createFileQualityCheck('validate-json', 'schemas', 'node scripts/ci/validate-json.mjs', 'scripts/ci/validate-json.mjs', options, 'Schema/fixture validation is tracked as a quality evidence route even when invoked directly.'),
  ];

  const dependencyBoundaries = [
    createDependencyBoundary('lint-deps-cycles', 'pnpm run lint:deps', 'lint:deps', scripts, options, 'src import graph', 'Madge circular import checks keep dependency cycles visible.'),
    createDependencyBoundary('context-pack-deps', 'pnpm run context-pack:deps', 'context-pack:deps', scripts, options, 'Context Pack implementation slices', 'Context Pack dependency checks prevent design boundary drift.'),
  ];

  const scriptWorkflowInventory = {
    packageScripts: createBucket(scriptNames),
    qualityScripts: createBucket(qualityScripts),
    ciScripts: createBucket(ciScripts),
    githubWorkflows: createBucket(workflows),
  };

  const debtLedgerSource = readDebtLedger(repoRoot, options.debtLedger);
  const debtLedger = {
    path: debtLedgerSource.path,
    exceptionCount: debtLedgerSource.items.length,
    items: debtLedgerSource.items,
  };
  const topCleanupCandidates = createTopCleanupCandidates(scriptWorkflowInventory, debtLedger.items);

  return {
    schemaVersion: SCHEMA_VERSION,
    contractId: CONTRACT_ID,
    generatedAt: options.generatedAt,
    repo: {
      name: packageJson.name ?? 'unknown',
      root: '.',
      packageManager: packageJson.packageManager ?? 'pnpm',
    },
    enforcement: {
      mode: 'report-only',
      policy: 'Issue #3547 establishes visibility first; ordinary PRs must not be blocked by this baseline until a later promotion issue changes policy.',
      ordinaryPrBlocking: false,
      promotionRule: 'Promote an individual metric only after the metric is deterministic, documented, fixture-backed, and explicitly added to the policy gate in a later PR.',
    },
    qualityChecks,
    architecturePlanes: createArchitecturePlanes(),
    scriptWorkflowInventory,
    publicEntrypoints: {
      packageBins: normalizeBinEntries(packageJson.bin),
      publicScripts: scriptNames
        .filter(isPublicScript)
        .map((name) => ({ name, command: scripts[name] })),
    },
    dependencyBoundaries,
    debtLedger,
    topCleanupCandidates,
    findings: createFindings(qualityChecks, dependencyBoundaries, debtLedger, topCleanupCandidates),
  };
}

function renderMarkdown(report) {
  const checkRows = report.qualityChecks.map((check) => `| ${check.id} | ${check.category} | \`${check.command}\` | ${check.status} | ${check.reportOnly ? 'yes' : 'no'} |`).join('\n');
  const boundaryRows = report.dependencyBoundaries.map((boundary) => `| ${boundary.id} | \`${boundary.command}\` | ${boundary.status} | ${boundary.scope} | ${boundary.guardrail} |`).join('\n');
  const planeRows = report.architecturePlanes.map((plane) => `| ${plane.plane} | ${plane.owner} | ${plane.primaryPaths.map((item) => `\`${item}\``).join('<br>')} | ${plane.guardrails.join('<br>')} |`).join('\n');
  const debtRows = report.debtLedger.items.length > 0
    ? report.debtLedger.items.map((item) => `| ${item.id} | ${item.owner} | ${item.reviewAfter} | ${item.targetCleanupSurface} | ${item.reason} |`).join('\n')
    : '| _none_ | _n/a_ | _n/a_ | _n/a_ | _n/a_ |';
  const cleanupRows = report.topCleanupCandidates.length > 0
    ? report.topCleanupCandidates.map((candidate) => `| ${candidate.id} | ${candidate.category} | ${candidate.severity} | ${candidate.target} | ${candidate.reason} |`).join('\n')
    : '| _none_ | _n/a_ | _n/a_ | _n/a_ | _n/a_ |';
  const inventoryRows = Object.entries(report.scriptWorkflowInventory)
    .map(([name, bucket]) => `| ${name} | ${bucket.count} | ${bucket.sample.map((item) => `\`${item}\``).join('<br>')} |`)
    .join('\n');
  const publicScriptRows = report.publicEntrypoints.publicScripts.length > 0
    ? report.publicEntrypoints.publicScripts.map((entry) => `| ${entry.name} | \`${entry.command}\` |`).join('\n')
    : '| _none_ | _n/a_ |';

  return `# Code Quality Baseline\n\nGenerated at: ${report.generatedAt}\n\n## Summary\n\n- Contract: \`${report.contractId}\` / \`${report.schemaVersion}\`\n- Enforcement mode: **${report.enforcement.mode}**\n- Ordinary PR blocking: **${report.enforcement.ordinaryPrBlocking ? 'yes' : 'no'}**\n- Debt ledger exceptions: **${report.debtLedger.exceptionCount}**\n- Cleanup candidates: **${report.topCleanupCandidates.length}**\n\n${report.enforcement.policy}\n\n## Quality checks\n\n| ID | Category | Command | Status | Report-only |\n| --- | --- | --- | --- | --- |\n${checkRows}\n\n## Dependency boundary checks\n\n| ID | Command | Status | Scope | Guardrail |\n| --- | --- | --- | --- | --- |\n${boundaryRows}\n\n## Architecture plane ownership\n\n| Plane | Owner | Primary paths | Guardrails |\n| --- | --- | --- | --- |\n${planeRows}\n\n## Script and workflow inventory\n\n| Bucket | Count | Sample |\n| --- | ---: | --- |\n${inventoryRows}\n\n## Public entrypoints\n\n### Package bins\n\n${report.publicEntrypoints.packageBins.map((entry) => `- \`${entry.name}\` -> \`${entry.path}\``).join('\n') || '- _none_'}\n\n### Public package scripts\n\n| Script | Command |\n| --- | --- |\n${publicScriptRows}\n\n## Debt ledger\n\nSource: \`${report.debtLedger.path}\`\n\n| ID | Owner | Review after | Target cleanup surface | Reason |\n| --- | --- | --- | --- | --- |\n${debtRows}\n\n## Top cleanup candidates\n\n| ID | Category | Severity | Target | Reason |\n| --- | --- | --- | --- | --- |\n${cleanupRows}\n\n## Promotion rule\n\n${report.enforcement.promotionRule}\n`;
}

function writeJson(filePath, payload) {
  fs.mkdirSync(path.dirname(filePath), { recursive: true });
  fs.writeFileSync(filePath, `${JSON.stringify(payload, null, 2)}\n`);
}

function writeText(filePath, text) {
  fs.mkdirSync(path.dirname(filePath), { recursive: true });
  fs.writeFileSync(filePath, text.endsWith('\n') ? text : `${text}\n`);
}

export function run(argv = process.argv.slice(2)) {
  const options = parseArgs(argv);
  if (options.help) {
    printHelp();
    return 0;
  }
  options.repoRoot = path.resolve(options.repoRoot);
  const report = collectCodeQualityBaseline(options);
  const outputJson = resolveFromRoot(options.repoRoot, options.outputJson);
  const outputMd = resolveFromRoot(options.repoRoot, options.outputMd);
  writeJson(outputJson, report);
  writeText(outputMd, renderMarkdown(report));
  process.stdout.write(`Wrote ${relativeFromRoot(options.repoRoot, outputJson)}\n`);
  process.stdout.write(`Wrote ${relativeFromRoot(options.repoRoot, outputMd)}\n`);
  return 0;
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
  try {
    process.exitCode = run();
  } catch (error) {
    console.error(error instanceof Error ? error.message : String(error));
    process.exitCode = 1;
  }
}
