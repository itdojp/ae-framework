#!/usr/bin/env node

import { spawnSync } from 'node:child_process';
import {
  cpus,
  totalmem,
  platform,
  arch,
} from 'node:os';
import {
  existsSync,
  mkdirSync,
  readFileSync,
  rmSync,
  writeFileSync,
} from 'node:fs';
import path from 'node:path';
import { performance } from 'node:perf_hooks';
import process from 'node:process';
import { fileURLToPath } from 'node:url';

const PHASES = [
  'actionInitialization',
  'corepackPnpmSetup',
  'dependencyInstall',
  'coreBuild',
  'gateExecution',
  'reviewSurfaceRendering',
  'total',
];

function parseArgs(argv) {
  const options = {
    runs: 5,
    fixture: 'pass',
    output: 'artifacts/benchmarks/assurance-gate-startup.json',
    outputMd: 'artifacts/benchmarks/assurance-gate-startup.md',
    workDir: '.codex-local/tmp/assurance-gate-startup-benchmark',
    actionRepo: process.cwd(),
    exactRef: '',
    runnerImage: process.env.ImageOS && process.env.ImageVersion
      ? `${process.env.ImageOS}-${process.env.ImageVersion}`
      : 'local-unpinned',
    checkoutInitializationMs: 0,
    pilotFriction: 'not-observed',
    help: false,
  };

  for (const arg of argv.slice(2)) {
    if (arg === '--') continue;
    if (arg === '--help' || arg === '-h') options.help = true;
    else if (arg.startsWith('--runs=')) options.runs = Number(arg.slice('--runs='.length));
    else if (arg.startsWith('--fixture=')) options.fixture = arg.slice('--fixture='.length);
    else if (arg.startsWith('--output=')) options.output = arg.slice('--output='.length);
    else if (arg.startsWith('--output-md=')) options.outputMd = arg.slice('--output-md='.length);
    else if (arg.startsWith('--work-dir=')) options.workDir = arg.slice('--work-dir='.length);
    else if (arg.startsWith('--action-repo=')) options.actionRepo = arg.slice('--action-repo='.length);
    else if (arg.startsWith('--exact-ref=')) options.exactRef = arg.slice('--exact-ref='.length);
    else if (arg.startsWith('--runner-image=')) options.runnerImage = arg.slice('--runner-image='.length);
    else if (arg.startsWith('--checkout-initialization-ms=')) {
      options.checkoutInitializationMs = Number(arg.slice('--checkout-initialization-ms='.length));
    } else if (arg.startsWith('--pilot-friction=')) {
      options.pilotFriction = arg.slice('--pilot-friction='.length);
    } else {
      throw new Error(`unknown argument: ${arg}`);
    }
  }

  if (!Number.isInteger(options.runs) || options.runs < 5) {
    throw new Error('--runs must be an integer >= 5');
  }
  if (!['pass', 'block'].includes(options.fixture)) {
    throw new Error('--fixture must be pass or block');
  }
  if (!['not-observed', 'observed'].includes(options.pilotFriction)) {
    throw new Error('--pilot-friction must be not-observed or observed');
  }
  if (!Number.isFinite(options.checkoutInitializationMs) || options.checkoutInitializationMs < 0) {
    throw new Error('--checkout-initialization-ms must be a non-negative number');
  }
  return options;
}

function printHelp() {
  process.stdout.write(`Usage: node scripts/actions/benchmark-assurance-gate-startup.mjs [options]\n\n`);
  process.stdout.write('Options:\n');
  process.stdout.write('  --runs=5                         measured samples per cold/warm state (minimum 5)\n');
  process.stdout.write('  --fixture=pass                   pass or block (block remains report-only)\n');
  process.stdout.write('  --output=<path>                  JSON report path\n');
  process.stdout.write('  --output-md=<path>               Markdown report path\n');
  process.stdout.write('  --work-dir=<path>                scratch directory inside the action repository\n');
  process.stdout.write('  --exact-ref=<sha>                exact measured action ref (defaults to git HEAD)\n');
  process.stdout.write('  --checkout-initialization-ms=0   workflow-observed checkout/init duration\n');
  process.stdout.write('  --pilot-friction=not-observed    not-observed or observed\n');
}

function assertInside(root, candidate, label) {
  const resolvedRoot = path.resolve(root);
  const resolved = path.resolve(candidate);
  const relative = path.relative(resolvedRoot, resolved);
  if (relative.startsWith('..') || path.isAbsolute(relative)) {
    throw new Error(`${label} must stay inside ${resolvedRoot}: ${resolved}`);
  }
  return resolved;
}

export function assertScratchDirectory(actionRepo, candidate) {
  const scratchRoot = path.join(actionRepo, '.codex-local', 'tmp');
  const resolved = assertInside(scratchRoot, candidate, 'work directory');
  if (path.relative(scratchRoot, resolved) === '') {
    throw new Error(`work directory must be a child of ${scratchRoot}`);
  }
  return resolved;
}

export function assertReportPath(actionRepo, candidate, extension, label) {
  const allowedRoots = [
    path.join(actionRepo, 'artifacts', 'benchmarks'),
    path.join(actionRepo, '.codex-local', 'tmp'),
  ];
  const resolved = path.resolve(candidate);
  const allowed = allowedRoots.some((root) => {
    const relative = path.relative(root, resolved);
    return relative !== '' && !relative.startsWith('..') && !path.isAbsolute(relative);
  });
  if (!allowed) {
    throw new Error(`${label} must be a file under artifacts/benchmarks or .codex-local/tmp`);
  }
  if (path.extname(resolved) !== extension) {
    throw new Error(`${label} must use the ${extension} extension`);
  }
  return resolved;
}

function assertBenchmarkRepository(actionRepo) {
  const expectedRoot = commandOutput('git', ['rev-parse', '--show-toplevel'], actionRepo);
  if (path.resolve(expectedRoot) !== actionRepo) {
    throw new Error(`action repository must be a Git worktree root: ${actionRepo}`);
  }
  for (const required of ['package.json', 'pnpm-lock.yaml', 'packages/core/package.json']) {
    const candidate = path.join(actionRepo, required);
    if (!existsSync(candidate)) {
      throw new Error(`action repository is missing ${required}: ${actionRepo}`);
    }
  }
}

function runCommand(command, args, { cwd, env = process.env, timeoutMs = 600_000, capture = false } = {}) {
  const startedAt = performance.now();
  const result = spawnSync(command, args, {
    cwd,
    env,
    encoding: 'utf8',
    timeout: timeoutMs,
    stdio: capture ? 'pipe' : 'inherit',
  });
  const durationMs = performance.now() - startedAt;
  if (result.error || result.status !== 0) {
    const detail = [result.error?.message, result.stderr, result.stdout].filter(Boolean).join('\n');
    const error = new Error(`${command} ${args.join(' ')} failed (${result.status ?? 'no status'}): ${detail}`);
    error.durationMs = durationMs;
    throw error;
  }
  return { durationMs, stdout: result.stdout?.trim() ?? '' };
}

function commandOutput(command, args, cwd) {
  return runCommand(command, args, { cwd, capture: true }).stdout;
}

function resetInstallState(actionRepo) {
  rmSync(path.join(actionRepo, 'node_modules'), { recursive: true, force: true });
  rmSync(path.join(actionRepo, 'packages', 'core', 'node_modules'), { recursive: true, force: true });
  rmSync(path.join(actionRepo, 'packages', 'core', 'dist'), { recursive: true, force: true });
}

function evidenceForFixture(fixture) {
  const evidence = fixture === 'pass'
    ? [
        {
          claimId: 'minimal-assurance-gate-reviewable',
          lane: 'spec',
          kind: 'schema',
          sourceKind: 'spec-derived',
          origin: 'startup-benchmark-fixture',
        },
        {
          claimId: 'minimal-assurance-gate-reviewable',
          lane: 'behavior',
          kind: 'integration',
          sourceKind: 'runtime-derived',
          origin: 'startup-benchmark-fixture',
        },
      ]
    : [
        {
          claimId: 'minimal-assurance-gate-reviewable',
          lane: 'spec',
          kind: 'schema',
          sourceKind: 'spec-derived',
          origin: 'startup-benchmark-fixture',
        },
      ];
  return {
    evidence,
    policyEvidence: fixture === 'pass'
      ? ['postDeployVerify', 'qualityGates']
      : ['postDeployVerify'],
  };
}

function initializeConsumerFixture(workRoot, cacheState, index, fixture) {
  const workspace = path.join(workRoot, 'consumer', `${cacheState}-${index}`);
  rmSync(workspace, { recursive: true, force: true });
  mkdirSync(path.join(workspace, 'artifacts'), { recursive: true });
  writeFileSync(
    path.join(workspace, 'artifacts', 'evidence.json'),
    `${JSON.stringify(evidenceForFixture(fixture), null, 2)}\n`,
  );
  return workspace;
}

function measureSample({ actionRepo, workRoot, cacheState, index, fixture, storeDir }) {
  if (cacheState === 'cold') {
    resetInstallState(actionRepo);
    rmSync(storeDir, { recursive: true, force: true });
  }
  mkdirSync(storeDir, { recursive: true });

  const totalStartedAt = performance.now();
  const phaseTimingsMs = Object.fromEntries(PHASES.map((phase) => [phase, 0]));
  let currentPhase = 'actionInitialization';
  let result = 'error';
  let errorPhase;
  try {
    const initStartedAt = performance.now();
    const workspace = initializeConsumerFixture(workRoot, cacheState, index, fixture);
    const timingOutput = path.join(workspace, 'artifacts', 'assurance-gate', 'internal-timing.json');
    phaseTimingsMs.actionInitialization = performance.now() - initStartedAt;

    currentPhase = 'corepackPnpmSetup';
    phaseTimingsMs.corepackPnpmSetup = runCommand(
      'bash',
      ['-lc', 'corepack enable && pnpm --version'],
      { cwd: actionRepo, capture: true },
    ).durationMs;
    currentPhase = 'dependencyInstall';
    phaseTimingsMs.dependencyInstall = runCommand('pnpm', [
      'install',
      '--frozen-lockfile',
      '--filter',
      '@ae-framework/core...',
      '--store-dir',
      storeDir,
    ], { cwd: actionRepo }).durationMs;
    currentPhase = 'coreBuild';
    phaseTimingsMs.coreBuild = runCommand(
      'pnpm',
      ['--filter', '@ae-framework/core', 'run', 'build'],
      { cwd: actionRepo },
    ).durationMs;
    currentPhase = 'gateExecution';
    phaseTimingsMs.gateExecution = runCommand('node', [
      'scripts/actions/assurance-gate.mjs',
      '--workspace', workspace,
      '--action-repo', actionRepo,
      '--profile', 'minimal',
      '--artifacts-dir', 'artifacts',
      '--output-dir', 'artifacts/assurance-gate',
      '--fail-on-block', 'false',
      '--timing-output', path.relative(workspace, timingOutput),
    ], { cwd: actionRepo }).durationMs;

    const timing = JSON.parse(readFileSync(timingOutput, 'utf8'));
    phaseTimingsMs.reviewSurfaceRendering = timing.reviewSurfaceRenderingMs;
    const gateResult = JSON.parse(readFileSync(
      path.join(workspace, 'artifacts', 'assurance-gate', 'gate-result.json'),
      'utf8',
    ));
    result = gateResult.policyResult;
  } catch (error) {
    errorPhase = currentPhase;
    if (error && typeof error === 'object' && Number.isFinite(error.durationMs)) {
      phaseTimingsMs[currentPhase] = error.durationMs;
    }
  }
  phaseTimingsMs.total = performance.now() - totalStartedAt;
  return {
    cacheState,
    index,
    result,
    ...(errorPhase ? { errorPhase } : {}),
    phaseTimingsMs,
  };
}

export function percentile(values, percentileValue) {
  if (!Array.isArray(values) || values.length === 0) throw new Error('values must not be empty');
  const sorted = [...values].sort((left, right) => left - right);
  const rank = Math.max(0, Math.ceil(percentileValue * sorted.length) - 1);
  return sorted[Math.min(rank, sorted.length - 1)];
}

export function summarizeValues(values) {
  const sorted = [...values].sort((left, right) => left - right);
  const middle = Math.floor(sorted.length / 2);
  const median = sorted.length % 2 === 0
    ? (sorted[middle - 1] + sorted[middle]) / 2
    : sorted[middle];
  return {
    minimum: sorted[0],
    median,
    maximum: sorted[sorted.length - 1],
    p90: percentile(sorted, 0.9),
  };
}

export function summarizeSamples(samples) {
  const result = {
    sampleCount: samples.length,
    results: {
      pass: samples.filter((sample) => sample.result === 'pass').length,
      block: samples.filter((sample) => sample.result === 'block').length,
      error: samples.filter((sample) => sample.result === 'error').length,
    },
    phaseTimingsMs: {},
  };
  for (const phase of PHASES) {
    result.phaseTimingsMs[phase] = summarizeValues(
      samples.map((sample) => sample.phaseTimingsMs[phase]),
    );
  }
  return result;
}

export function assessOptimization(summary, pilotFriction) {
  const cold = summary.cold.phaseTimingsMs;
  const setupInstallBuild = cold.corepackPnpmSetup.median
    + cold.dependencyInstall.median
    + cold.coreBuild.median;
  const setupInstallBuildShare = cold.total.median > 0
    ? setupInstallBuild / cold.total.median
    : 0;
  const triggers = {
    coldMedianOver60Seconds: cold.total.median > 60_000,
    setupInstallBuildOver70Percent: setupInstallBuildShare > 0.7,
    livePilotFrictionObserved: pilotFriction === 'observed',
  };
  const triggered = Object.values(triggers).some(Boolean);
  return {
    status: 'baseline-assessment',
    triggers,
    setupInstallBuildShare,
    recommendedOutcome: triggered ? 'evaluate-one-low-risk-optimization' : 'maintain-current-runtime',
    finalDecision: 'pending-reviewed-baseline',
  };
}

export function renderMarkdown(report) {
  const lines = [
    '# Assurance Gate startup benchmark',
    '',
    `- Exact ref: \`${report.exactRef}\``,
    `- Fixture: \`${report.fixture.id}\` (${report.fixture.expectedResult})`,
    `- Runner: ${report.environment.runnerOs}/${report.environment.architecture} (${report.environment.runnerImage})`,
    `- Node/npm/pnpm: ${report.environment.nodeVersion} / ${report.environment.npmVersion} / ${report.environment.pnpmVersion}`,
    `- Samples: cold=${report.summary.cold.sampleCount}, warm=${report.summary.warm.sampleCount}`,
    `- Cold results: pass=${report.summary.cold.results.pass}, block=${report.summary.cold.results.block}, error=${report.summary.cold.results.error}`,
    `- Warm results: pass=${report.summary.warm.results.pass}, block=${report.summary.warm.results.block}, error=${report.summary.warm.results.error}`,
    `- Workflow checkout/initialization: ${report.method.checkoutInitializationMs.toFixed(2)} ms (recorded once, outside per-sample total)`,
    '',
    '| Cache | Phase | Minimum (ms) | Median (ms) | Maximum (ms) | p90 (ms) |',
    '| --- | --- | ---: | ---: | ---: | ---: |',
  ];
  for (const cacheState of ['cold', 'warm']) {
    for (const phase of PHASES) {
      const stats = report.summary[cacheState].phaseTimingsMs[phase];
      lines.push(`| ${cacheState} | ${phase} | ${stats.minimum.toFixed(2)} | ${stats.median.toFixed(2)} | ${stats.maximum.toFixed(2)} | ${stats.p90.toFixed(2)} |`);
    }
  }
  const errorSamples = report.samples.filter((sample) => sample.result === 'error');
  if (errorSamples.length > 0) {
    lines.push(
      '',
      '## Measurement errors',
      '',
      ...errorSamples.map((sample) => `- ${sample.cacheState} #${sample.index}: ${sample.errorPhase}`),
    );
  }
  lines.push(
    '',
    '## Optimization assessment',
    '',
    `- Cold median total > 60s: ${report.optimizationAssessment.triggers.coldMedianOver60Seconds}`,
    `- Setup + install + build > 70%: ${report.optimizationAssessment.triggers.setupInstallBuildOver70Percent}`,
    `- Setup/install/build share: ${(report.optimizationAssessment.setupInstallBuildShare * 100).toFixed(2)}%`,
    `- Live pilot friction observed: ${report.optimizationAssessment.triggers.livePilotFrictionObserved}`,
    `- Recommended outcome: \`${report.optimizationAssessment.recommendedOutcome}\``,
    `- Final decision: \`${report.optimizationAssessment.finalDecision}\``,
    '',
    '> This report measures startup/runtime overhead only. It is not evidence of review speed, productivity, code quality, approval, or safety improvement.',
    '',
  );
  return lines.join('\n');
}

function resolveExactRef(actionRepo, requestedRef) {
  if (requestedRef) return requestedRef;
  return commandOutput('git', ['rev-parse', 'HEAD'], actionRepo);
}

function buildEnvironment(actionRepo, options) {
  return {
    runnerOs: platform(),
    architecture: arch(),
    runnerImage: options.runnerImage,
    cpu: cpus()[0]?.model ?? 'unknown',
    totalMemoryBytes: totalmem(),
    nodeVersion: process.version,
    npmVersion: commandOutput('npm', ['--version'], actionRepo),
    pnpmVersion: commandOutput('pnpm', ['--version'], actionRepo),
  };
}

function warmInstallState(actionRepo, storeDir) {
  resetInstallState(actionRepo);
  rmSync(storeDir, { recursive: true, force: true });
  mkdirSync(storeDir, { recursive: true });
  runCommand('bash', ['-lc', 'corepack enable && pnpm --version'], { cwd: actionRepo, capture: true });
  runCommand('pnpm', [
    'install',
    '--frozen-lockfile',
    '--filter',
    '@ae-framework/core...',
    '--store-dir',
    storeDir,
  ], { cwd: actionRepo });
  runCommand('pnpm', ['--filter', '@ae-framework/core', 'run', 'build'], { cwd: actionRepo });
}

export function runBenchmark(options) {
  const actionRepo = path.resolve(options.actionRepo);
  assertBenchmarkRepository(actionRepo);
  const workRoot = assertScratchDirectory(actionRepo, path.resolve(actionRepo, options.workDir));
  const outputPath = assertReportPath(
    actionRepo,
    path.resolve(actionRepo, options.output),
    '.json',
    'JSON output',
  );
  const outputMdPath = assertReportPath(
    actionRepo,
    path.resolve(actionRepo, options.outputMd),
    '.md',
    'Markdown output',
  );
  rmSync(workRoot, { recursive: true, force: true });
  mkdirSync(workRoot, { recursive: true });

  const samples = [];
  for (let index = 1; index <= options.runs; index += 1) {
    samples.push(measureSample({
      actionRepo,
      workRoot,
      cacheState: 'cold',
      index,
      fixture: options.fixture,
      storeDir: path.join(workRoot, 'stores', `cold-${index}`),
    }));
  }

  const warmStore = path.join(workRoot, 'stores', 'warm');
  warmInstallState(actionRepo, warmStore);
  for (let index = 1; index <= options.runs; index += 1) {
    samples.push(measureSample({
      actionRepo,
      workRoot,
      cacheState: 'warm',
      index,
      fixture: options.fixture,
      storeDir: warmStore,
    }));
  }

  const summary = {
    cold: summarizeSamples(samples.filter((sample) => sample.cacheState === 'cold')),
    warm: summarizeSamples(samples.filter((sample) => sample.cacheState === 'warm')),
  };
  const report = {
    schemaVersion: 'assurance-gate-startup-benchmark/v1',
    generatedAt: new Date().toISOString(),
    exactRef: resolveExactRef(actionRepo, options.exactRef),
    fixture: {
      id: `external-minimal-${options.fixture}`,
      expectedResult: options.fixture,
      profile: 'minimal',
    },
    environment: buildEnvironment(actionRepo, options),
    method: {
      runCountPerCacheState: options.runs,
      checkoutInitializationMs: options.checkoutInitializationMs,
      pilotFriction: options.pilotFriction,
      coldDefinition: 'Remove node_modules/core dist and use a unique empty pnpm store before every measured sample.',
      warmDefinition: 'Precondition one pnpm store and linked node_modules/core build, then execute the unchanged action setup/install/build/gate path for every measured sample.',
      reviewSurfaceTimingBoundary: 'reviewSurfaceRendering is an internal subphase of gateExecution and is not added again to total.',
    },
    samples,
    summary,
    optimizationAssessment: assessOptimization(summary, options.pilotFriction),
  };
  mkdirSync(path.dirname(outputPath), { recursive: true });
  mkdirSync(path.dirname(outputMdPath), { recursive: true });
  writeFileSync(outputPath, `${JSON.stringify(report, null, 2)}\n`);
  writeFileSync(outputMdPath, `${renderMarkdown(report)}\n`);
  return { report, outputPath, outputMdPath };
}

export function isExecutedAsMain(metaUrl, argvPath = process.argv[1]) {
  if (!argvPath) return false;
  return path.resolve(fileURLToPath(metaUrl)) === path.resolve(argvPath);
}

if (isExecutedAsMain(import.meta.url)) {
  try {
    const options = parseArgs(process.argv);
    if (options.help) {
      printHelp();
    } else {
      const result = runBenchmark(options);
      process.stdout.write(`- JSON: ${path.relative(process.cwd(), result.outputPath)}\n`);
      process.stdout.write(`- Markdown: ${path.relative(process.cwd(), result.outputMdPath)}\n`);
      const errorCount = result.report.samples.filter((sample) => sample.result === 'error').length;
      if (errorCount > 0) {
        throw new Error(`${errorCount} measured sample(s) ended in error; reports were preserved`);
      }
      process.stdout.write(`Assurance Gate startup benchmark: OK\n`);
    }
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    process.stderr.write(`Assurance Gate startup benchmark: FAILED\n${message}\n`);
    process.exitCode = 1;
  }
}
