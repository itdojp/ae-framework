#!/usr/bin/env node

import { Command } from 'commander';
import chalk from 'chalk';
import * as fs from 'node:fs/promises';
import * as path from 'node:path';
import yaml from 'yaml';
import { toMessage } from '../utils/error-utils.js';
import { safeExit } from '../utils/safe-exit.js';

export type SignalComparison = 'lte' | 'gte';
export type SignalStatus = 'pass' | 'warn' | 'fail' | 'unknown';
export type ReleaseVerifyStatus = 'pass' | 'warn' | 'fail';

export interface ReleasePolicySignal {
  metricKey: string;
  warningThreshold: number;
  criticalThreshold: number;
  comparison: SignalComparison;
}

export interface ReleasePolicyHook {
  type: 'command' | 'none';
  command?: string;
  timeoutSeconds: number;
}

export interface ReleasePolicyEnvironment {
  percentSteps: number[];
  pauseSeconds: number;
  requiredEvidence: string[];
}

export interface ReleasePolicy {
  schemaVersion: 'ae-release-policy/v1';
  version: number;
  updatedAt: string;
  owner: string;
  rolloutStrategy: {
    mode: 'canary' | 'progressive' | 'blue-green';
    percentSteps: number[];
    pauseSeconds: number;
    maxDurationSeconds: number;
  };
  healthSignals: Record<string, ReleasePolicySignal>;
  rollbackPolicy: {
    enabled: boolean;
    trigger: 'any-critical' | 'all-critical' | 'manual';
    dryRun: boolean;
    hook: ReleasePolicyHook;
  };
  requiredEvidence: string[];
  environments: Record<string, ReleasePolicyEnvironment>;
}

export interface ReleasePlan {
  schemaVersion: 'ae-release-plan/v1';
  generatedAt: string;
  policy: {
    version: number;
    updatedAt: string;
    owner: string;
  };
  environment: string;
  featureName: string | null;
  rollout: {
    mode: string;
    percentSteps: number[];
    pauseSeconds: number;
    maxDurationSeconds: number;
  };
  healthSignals: Array<{
    name: string;
    metricKey: string;
    comparison: SignalComparison;
    warningThreshold: number;
    criticalThreshold: number;
  }>;
  rollbackPolicy: {
    enabled: boolean;
    trigger: string;
    dryRun: boolean;
    hook: ReleasePolicyHook;
  };
  requiredEvidence: string[];
}

export interface ReleaseSignalEvaluation {
  name: string;
  metricKey: string;
  comparison: SignalComparison;
  warningThreshold: number;
  criticalThreshold: number;
  observed: number | null;
  status: SignalStatus;
  reason: string;
}

export interface ReleaseEvidenceEvaluation {
  name: string;
  present: boolean;
  source: string;
  reason: string;
}

export interface ReleaseVerifyResult {
  schemaVersion: 'ae-post-deploy-verify/v1';
  generatedAt: string;
  environment: string;
  status: ReleaseVerifyStatus;
  rollbackRecommended: boolean;
  summary: {
    passSignals: number;
    warnSignals: number;
    failSignals: number;
    unknownSignals: number;
    missingEvidence: string[];
  };
  inputs: {
    metricsPath: string;
    traceBundlePath: string | null;
    syntheticChecksPath: string | null;
  };
  signals: ReleaseSignalEvaluation[];
  evidence: ReleaseEvidenceEvaluation[];
  rollback: {
    enabled: boolean;
    trigger: string;
    dryRun: boolean;
    hook: ReleasePolicyHook;
  };
}

const DEFAULT_POLICY_PATH = 'policy/release-policy.yml';
const DEFAULT_RELEASE_ARTIFACT_DIR = path.join('artifacts', 'release');
const RELEASE_ROLLOUT_MODES = ['canary', 'progressive', 'blue-green'] as const;
const RELEASE_SIGNAL_COMPARISONS = ['lte', 'gte'] as const;
const ROLLBACK_TRIGGERS = ['any-critical', 'all-critical', 'manual'] as const;
const ROLLBACK_HOOK_TYPES = ['command', 'none'] as const;

const isRecord = (value: unknown): value is Record<string, unknown> =>
  typeof value === 'object' && value !== null;

const isOneOf = <T extends readonly string[]>(value: string, candidates: T): value is T[number] =>
  candidates.includes(value as T[number]);

const toNumber = (value: unknown): number | null => {
  if (typeof value === 'number' && Number.isFinite(value)) {
    return value;
  }
  if (typeof value === 'string' && value.trim() !== '') {
    const parsed = Number(value);
    return Number.isFinite(parsed) ? parsed : null;
  }
  return null;
};

const normalizeStringArray = (value: unknown): string[] => {
  if (!Array.isArray(value)) return [];
  return value.map((item) => String(item)).filter((item) => item.trim() !== '');
};

const loadStructuredFile = async (filePath: string): Promise<unknown> => {
  const absolutePath = path.resolve(filePath);
  const raw = await fs.readFile(absolutePath, 'utf8');
  const extension = path.extname(absolutePath).toLowerCase();
  if (extension === '.yaml' || extension === '.yml') {
    return yaml.parse(raw);
  }
  return JSON.parse(raw);
};

const resolveEnvironment = (policy: ReleasePolicy, environment: string): ReleasePolicyEnvironment => {
  const entry = policy.environments[environment];
  if (!entry) {
    throw new Error(`Environment '${environment}' is not defined in policy`);
  }
  return entry;
};

const isValidThresholdOrder = (
  comparison: SignalComparison,
  warningThreshold: number,
  criticalThreshold: number,
): boolean => {
  if (comparison === 'lte') {
    return warningThreshold <= criticalThreshold;
  }
  return warningThreshold >= criticalThreshold;
};

export const parseReleasePolicy = (input: unknown): ReleasePolicy => {
  if (!isRecord(input)) {
    throw new Error('release policy must be an object');
  }

  const schemaVersion = String(input['schemaVersion'] ?? '');
  if (schemaVersion !== 'ae-release-policy/v1') {
    throw new Error(`unsupported schemaVersion: ${schemaVersion || '(empty)'}`);
  }

  const rolloutStrategy = input['rolloutStrategy'];
  if (!isRecord(rolloutStrategy)) {
    throw new Error('rolloutStrategy is required');
  }

  const rollbackPolicy = input['rollbackPolicy'];
  if (!isRecord(rollbackPolicy)) {
    throw new Error('rollbackPolicy is required');
  }
  const hook = rollbackPolicy['hook'];
  if (!isRecord(hook)) {
    throw new Error('rollbackPolicy.hook is required');
  }

  const environmentsValue = input['environments'];
  if (!isRecord(environmentsValue)) {
    throw new Error('environments is required');
  }

  const healthSignalsValue = input['healthSignals'];
  if (!isRecord(healthSignalsValue)) {
    throw new Error('healthSignals is required');
  }

  const rolloutMode = String(rolloutStrategy['mode'] ?? 'canary');
  if (!isOneOf(rolloutMode, RELEASE_ROLLOUT_MODES)) {
    throw new Error(`rolloutStrategy.mode has invalid value: ${rolloutMode}`);
  }

  const rollbackTrigger = String(rollbackPolicy['trigger'] ?? 'manual');
  if (!isOneOf(rollbackTrigger, ROLLBACK_TRIGGERS)) {
    throw new Error(`rollbackPolicy.trigger has invalid value: ${rollbackTrigger}`);
  }

  const hookType = String(hook['type'] ?? 'none');
  if (!isOneOf(hookType, ROLLBACK_HOOK_TYPES)) {
    throw new Error(`rollbackPolicy.hook.type has invalid value: ${hookType}`);
  }

  const hookTimeoutSeconds = toNumber(hook['timeoutSeconds']);
  if (hookTimeoutSeconds === null || !Number.isInteger(hookTimeoutSeconds) || hookTimeoutSeconds < 1) {
    throw new Error('rollbackPolicy.hook.timeoutSeconds must be an integer >= 1');
  }

  const hookCommandValue = typeof hook['command'] === 'string' ? hook['command'].trim() : '';
  if (hookType === 'command' && hookCommandValue === '') {
    throw new Error('rollbackPolicy.hook.command is required when hook.type=command');
  }
  if (hookType === 'none' && hookCommandValue !== '') {
    throw new Error('rollbackPolicy.hook.command must be empty when hook.type=none');
  }

  const parsedSignals: Record<string, ReleasePolicySignal> = {};
  for (const [name, rawSignal] of Object.entries(healthSignalsValue)) {
    if (!isRecord(rawSignal)) {
      throw new Error(`healthSignals.${name} must be an object`);
    }
    const warningThreshold = toNumber(rawSignal['warningThreshold']);
    const criticalThreshold = toNumber(rawSignal['criticalThreshold']);
    const comparisonValue = String(rawSignal['comparison'] ?? '');
    const metricKey = String(rawSignal['metricKey'] ?? '').trim();
    if (
      warningThreshold === null ||
      criticalThreshold === null ||
      !isOneOf(comparisonValue, RELEASE_SIGNAL_COMPARISONS)
    ) {
      throw new Error(`healthSignals.${name} has invalid threshold/comparison`);
    }
    const comparison: SignalComparison = comparisonValue;
    if (!metricKey) {
      throw new Error(`healthSignals.${name}.metricKey is required`);
    }
    if (!isValidThresholdOrder(comparison, warningThreshold, criticalThreshold)) {
      throw new Error(`healthSignals.${name} has invalid warning/critical threshold order`);
    }
    parsedSignals[name] = {
      metricKey,
      warningThreshold,
      criticalThreshold,
      comparison,
    };
  }

  const parsedEnvironments: Record<string, ReleasePolicyEnvironment> = {};
  for (const [name, rawEnv] of Object.entries(environmentsValue)) {
    if (!isRecord(rawEnv)) {
      throw new Error(`environments.${name} must be an object`);
    }
    const percentSteps = Array.isArray(rawEnv['percentSteps'])
      ? rawEnv['percentSteps']
          .map((value) => toNumber(value))
          .filter((value): value is number => value !== null)
      : [];
    parsedEnvironments[name] = {
      percentSteps,
      pauseSeconds: toNumber(rawEnv['pauseSeconds']) ?? 0,
      requiredEvidence: normalizeStringArray(rawEnv['requiredEvidence']),
    };
  }

  const rolloutPercentSteps = Array.isArray(rolloutStrategy['percentSteps'])
    ? rolloutStrategy['percentSteps']
        .map((value) => toNumber(value))
        .filter((value): value is number => value !== null)
    : [];
  const hookSettings: ReleasePolicyHook =
    hookType === 'command'
      ? {
          type: 'command',
          command: hookCommandValue,
          timeoutSeconds: hookTimeoutSeconds,
        }
      : {
          type: 'none',
          timeoutSeconds: hookTimeoutSeconds,
        };

  return {
    schemaVersion: 'ae-release-policy/v1',
    version: toNumber(input['version']) ?? 1,
    updatedAt: String(input['updatedAt'] ?? ''),
    owner: String(input['owner'] ?? ''),
    rolloutStrategy: {
      mode: rolloutMode,
      percentSteps: rolloutPercentSteps,
      pauseSeconds: toNumber(rolloutStrategy['pauseSeconds']) ?? 0,
      maxDurationSeconds: toNumber(rolloutStrategy['maxDurationSeconds']) ?? 0,
    },
    healthSignals: parsedSignals,
    rollbackPolicy: {
      enabled: Boolean(rollbackPolicy['enabled']),
      trigger: rollbackTrigger,
      dryRun: Boolean(rollbackPolicy['dryRun']),
      hook: hookSettings,
    },
    requiredEvidence: normalizeStringArray(input['requiredEvidence']),
    environments: parsedEnvironments,
  };
};

const signalStatusFromThreshold = (
  value: number,
  signal: ReleasePolicySignal,
): SignalStatus => {
  if (signal.comparison === 'lte') {
    if (value <= signal.warningThreshold) return 'pass';
    if (value <= signal.criticalThreshold) return 'warn';
    return 'fail';
  }
  if (value >= signal.warningThreshold) return 'pass';
  if (value >= signal.criticalThreshold) return 'warn';
  return 'fail';
};

const signalReason = (
  status: SignalStatus,
  signal: ReleasePolicySignal,
): string => {
  if (status === 'unknown') {
    return 'metric missing in snapshot';
  }
  if (status === 'pass') {
    return `within warning threshold (${signal.comparison} ${signal.warningThreshold})`;
  }
  if (status === 'warn') {
    return `outside warning threshold, within critical threshold (${signal.comparison} ${signal.criticalThreshold})`;
  }
  return `outside critical threshold (${signal.comparison} ${signal.criticalThreshold})`;
};

const extractMetrics = (snapshot: unknown): Record<string, number> => {
  if (!isRecord(snapshot)) {
    throw new Error('metrics snapshot must be an object');
  }
  const metrics: Record<string, number> = {};
  for (const [key, value] of Object.entries(snapshot)) {
    const asNumber = toNumber(value);
    if (asNumber !== null) {
      metrics[key] = asNumber;
    }
  }
  if (isRecord(snapshot['metrics'])) {
    for (const [key, value] of Object.entries(snapshot['metrics'])) {
      const asNumber = toNumber(value);
      if (asNumber !== null) {
        metrics[key] = asNumber;
      }
    }
  }
  return metrics;
};

export const buildReleasePlan = (
  policy: ReleasePolicy,
  environment: string,
  featureName?: string,
): ReleasePlan => {
  const environmentPolicy = resolveEnvironment(policy, environment);
  const requiredEvidence = Array.from(
    new Set([...policy.requiredEvidence, ...environmentPolicy.requiredEvidence]),
  );
  return {
    schemaVersion: 'ae-release-plan/v1',
    generatedAt: new Date().toISOString(),
    policy: {
      version: policy.version,
      updatedAt: policy.updatedAt,
      owner: policy.owner,
    },
    environment,
    featureName: featureName?.trim() || null,
    rollout: {
      mode: policy.rolloutStrategy.mode,
      percentSteps:
        environmentPolicy.percentSteps.length > 0
          ? environmentPolicy.percentSteps
          : policy.rolloutStrategy.percentSteps,
      pauseSeconds: environmentPolicy.pauseSeconds,
      maxDurationSeconds: policy.rolloutStrategy.maxDurationSeconds,
    },
    healthSignals: Object.entries(policy.healthSignals).map(([name, signal]) => ({
      name,
      metricKey: signal.metricKey,
      comparison: signal.comparison,
      warningThreshold: signal.warningThreshold,
      criticalThreshold: signal.criticalThreshold,
    })),
    rollbackPolicy: {
      enabled: policy.rollbackPolicy.enabled,
      trigger: policy.rollbackPolicy.trigger,
      dryRun: policy.rollbackPolicy.dryRun,
      hook: policy.rollbackPolicy.hook,
    },
    requiredEvidence,
  };
};

export const evaluateReleaseVerify = (
  policy: ReleasePolicy,
  environment: string,
  metricsSnapshot: unknown,
  traceBundle: unknown | null,
  syntheticChecks: unknown | null,
  metricsPath: string,
  traceBundlePath: string | null,
  syntheticChecksPath: string | null,
): ReleaseVerifyResult => {
  const environmentPolicy = resolveEnvironment(policy, environment);
  const metrics = extractMetrics(metricsSnapshot);

  const signals = Object.entries(policy.healthSignals).map(([name, signal]) => {
    const observed = metrics[signal.metricKey] ?? null;
    const status = observed === null ? 'unknown' : signalStatusFromThreshold(observed, signal);
    return {
      name,
      metricKey: signal.metricKey,
      comparison: signal.comparison,
      warningThreshold: signal.warningThreshold,
      criticalThreshold: signal.criticalThreshold,
      observed,
      status,
      reason: signalReason(status, signal),
    } satisfies ReleaseSignalEvaluation;
  });

  const requiredEvidence = Array.from(
    new Set([...policy.requiredEvidence, ...environmentPolicy.requiredEvidence]),
  );
  const syntheticPass =
    isRecord(syntheticChecks) &&
    (syntheticChecks['ok'] === true ||
      syntheticChecks['status'] === 'pass' ||
      syntheticChecks['status'] === 'success');

  const evidence = requiredEvidence.map((name) => {
    if (name === 'postDeployVerify') {
      return {
        name,
        present: true,
        source: 'release-verify',
        reason: 'generated by this command',
      } satisfies ReleaseEvidenceEvaluation;
    }
    if (name === 'conformanceSummary') {
      return {
        name,
        present: Boolean(traceBundle),
        source: 'trace-bundle',
        reason: traceBundle ? 'trace bundle provided' : 'trace bundle not provided',
      } satisfies ReleaseEvidenceEvaluation;
    }
    if (name === 'qualityGates') {
      return {
        name,
        present: syntheticPass,
        source: 'synthetic-checks',
        reason: syntheticPass
          ? 'synthetic checks are pass/success'
          : 'synthetic checks missing or not pass',
      } satisfies ReleaseEvidenceEvaluation;
    }
    return {
      name,
      present: false,
      source: 'unknown',
      reason: 'unsupported evidence source',
    } satisfies ReleaseEvidenceEvaluation;
  });

  const failSignals = signals.filter((signal) => signal.status === 'fail').length;
  const warnSignals = signals.filter((signal) => signal.status === 'warn').length;
  const unknownSignals = signals.filter((signal) => signal.status === 'unknown').length;
  const passSignals = signals.filter((signal) => signal.status === 'pass').length;
  const missingEvidence = evidence.filter((item) => !item.present).map((item) => item.name);

  let status: ReleaseVerifyStatus = 'pass';
  if (failSignals > 0) {
    status = 'fail';
  } else if (warnSignals > 0 || unknownSignals > 0 || missingEvidence.length > 0) {
    status = 'warn';
  }

  const totalSignals = signals.length;
  const rollbackTriggered =
    policy.rollbackPolicy.trigger === 'any-critical'
      ? failSignals > 0
      : policy.rollbackPolicy.trigger === 'all-critical'
        ? totalSignals > 0 && failSignals === totalSignals
        : false;

  return {
    schemaVersion: 'ae-post-deploy-verify/v1',
    generatedAt: new Date().toISOString(),
    environment,
    status,
    rollbackRecommended: status === 'fail' && policy.rollbackPolicy.enabled && rollbackTriggered,
    summary: {
      passSignals,
      warnSignals,
      failSignals,
      unknownSignals,
      missingEvidence,
    },
    inputs: {
      metricsPath,
      traceBundlePath,
      syntheticChecksPath,
    },
    signals,
    evidence,
    rollback: {
      enabled: policy.rollbackPolicy.enabled,
      trigger: policy.rollbackPolicy.trigger,
      dryRun: policy.rollbackPolicy.dryRun,
      hook: policy.rollbackPolicy.hook,
    },
  };
};

const renderPlanMarkdown = (plan: ReleasePlan): string => {
  const formatSignalLine = (signal: ReleasePlan['healthSignals'][number]): string => {
    if (signal.comparison === 'lte') {
      return `- ${signal.name}: key=${signal.metricKey}, pass<=${signal.warningThreshold}, warn<=${signal.criticalThreshold}, fail>${signal.criticalThreshold}`;
    }
    return `- ${signal.name}: key=${signal.metricKey}, pass>=${signal.warningThreshold}, warn>=${signal.criticalThreshold}, fail<${signal.criticalThreshold}`;
  };

  const lines = [
    '## Release Plan',
    `- generatedAt: ${plan.generatedAt}`,
    `- environment: ${plan.environment}`,
    `- feature: ${plan.featureName ?? '(none)'}`,
    `- rollout mode: ${plan.rollout.mode}`,
    `- percent steps: ${plan.rollout.percentSteps.join(' -> ')}`,
    `- pause seconds: ${plan.rollout.pauseSeconds}`,
    `- max duration seconds: ${plan.rollout.maxDurationSeconds}`,
    '',
    '### Health Signals',
    ...plan.healthSignals.map((signal) => formatSignalLine(signal)),
    '',
    '### Required Evidence',
    ...plan.requiredEvidence.map((item) => `- ${item}`),
  ];
  return `${lines.join('\n')}\n`;
};

const renderVerifyMarkdown = (verify: ReleaseVerifyResult): string => {
  const lines = [
    '## Post-Deploy Verify',
    `- generatedAt: ${verify.generatedAt}`,
    `- environment: ${verify.environment}`,
    `- status: ${verify.status}`,
    `- rollback recommended: ${verify.rollbackRecommended ? 'yes' : 'no'}`,
    `- signals: pass=${verify.summary.passSignals}, warn=${verify.summary.warnSignals}, fail=${verify.summary.failSignals}, unknown=${verify.summary.unknownSignals}`,
    `- missing evidence: ${verify.summary.missingEvidence.length === 0 ? '(none)' : verify.summary.missingEvidence.join(', ')}`,
    '',
    '### Signal Details',
    ...verify.signals.map(
      (signal) =>
        `- ${signal.name}: ${signal.status} (metric=${signal.metricKey}, observed=${signal.observed ?? 'missing'}, reason=${signal.reason})`,
    ),
    '',
    '### Evidence',
    ...verify.evidence.map(
      (item) => `- ${item.name}: ${item.present ? 'present' : 'missing'} (${item.reason})`,
    ),
  ];
  return `${lines.join('\n')}\n`;
};

const writeArtifacts = async (jsonPath: string, markdownPath: string, payload: unknown, markdown: string) => {
  await fs.mkdir(path.dirname(jsonPath), { recursive: true });
  await fs.mkdir(path.dirname(markdownPath), { recursive: true });
  await fs.writeFile(jsonPath, `${JSON.stringify(payload, null, 2)}\n`, 'utf8');
  await fs.writeFile(markdownPath, markdown, 'utf8');
};

const loadPolicyFile = async (policyPath: string): Promise<ReleasePolicy> => {
  const rawPolicy = await loadStructuredFile(policyPath);
  return parseReleasePolicy(rawPolicy);
};

export function createReleaseCommand(): Command {
  const command = new Command('release');
  command.description('Release engineering commands');

  command
    .command('plan')
    .description('Generate release plan from release-policy')
    .option('--policy <path>', 'Release policy path', DEFAULT_POLICY_PATH)
    .option('--environment <name>', 'Environment name', 'staging')
    .option('--feature <name>', 'Feature or rollout target name')
    .option('--output-dir <dir>', 'Output directory', DEFAULT_RELEASE_ARTIFACT_DIR)
    .option('--json-out <path>', 'Release plan JSON output path')
    .option('--md-out <path>', 'Release plan markdown output path')
    .action(async (options) => {
      try {
        const policyPath = path.resolve(options.policy);
        const policy = await loadPolicyFile(policyPath);
        const environment = String(options.environment || 'staging');
        const plan = buildReleasePlan(policy, environment, options.feature);
        const outputDir = path.resolve(options.outputDir || DEFAULT_RELEASE_ARTIFACT_DIR);
        const jsonOut = path.resolve(options.jsonOut || path.join(outputDir, 'release-plan.json'));
        const mdOut = path.resolve(options.mdOut || path.join(outputDir, 'release-plan.md'));
        await writeArtifacts(jsonOut, mdOut, plan, renderPlanMarkdown(plan));

        console.log(chalk.green('✅ release plan generated'));
        console.log(chalk.gray(`   json: ${jsonOut}`));
        console.log(chalk.gray(`   markdown: ${mdOut}`));
      } catch (error: unknown) {
        console.error(chalk.red(`❌ release plan failed: ${toMessage(error)}`));
        safeExit(1);
      }
    });

  command
    .command('verify')
    .description('Evaluate post-deploy metrics against release-policy')
    .requiredOption('--metrics <path>', 'Metrics snapshot JSON/YAML path')
    .option('--policy <path>', 'Release policy path', DEFAULT_POLICY_PATH)
    .option('--environment <name>', 'Environment name', 'staging')
    .option('--trace-bundle <path>', 'Trace bundle JSON path')
    .option('--synthetic-checks <path>', 'Synthetic checks result JSON path')
    .option('--output-dir <dir>', 'Output directory', DEFAULT_RELEASE_ARTIFACT_DIR)
    .option('--json-out <path>', 'Post-deploy verify JSON output path')
    .option('--md-out <path>', 'Post-deploy verify markdown output path')
    .option('--strict', 'Exit with non-zero status when verify result is fail', false)
    .action(async (options) => {
      try {
        const policyPath = path.resolve(options.policy);
        const policy = await loadPolicyFile(policyPath);
        const metricsPath = path.resolve(options.metrics);
        const metrics = await loadStructuredFile(metricsPath);
        const traceBundlePath = options.traceBundle ? path.resolve(options.traceBundle) : null;
        const traceBundle = traceBundlePath ? await loadStructuredFile(traceBundlePath) : null;
        const syntheticChecksPath = options.syntheticChecks
          ? path.resolve(options.syntheticChecks)
          : null;
        const syntheticChecks = syntheticChecksPath
          ? await loadStructuredFile(syntheticChecksPath)
          : null;

        const result = evaluateReleaseVerify(
          policy,
          String(options.environment || 'staging'),
          metrics,
          traceBundle,
          syntheticChecks,
          metricsPath,
          traceBundlePath,
          syntheticChecksPath,
        );

        const outputDir = path.resolve(options.outputDir || DEFAULT_RELEASE_ARTIFACT_DIR);
        const jsonOut = path.resolve(
          options.jsonOut || path.join(outputDir, 'post-deploy-verify.json'),
        );
        const mdOut = path.resolve(
          options.mdOut || path.join(outputDir, 'post-deploy-verify.md'),
        );

        await writeArtifacts(jsonOut, mdOut, result, renderVerifyMarkdown(result));

        const statusColor =
          result.status === 'pass'
            ? chalk.green
            : result.status === 'warn'
              ? chalk.yellow
              : chalk.red;
        console.log(statusColor(`✅ release verify status: ${result.status}`));
        console.log(chalk.gray(`   json: ${jsonOut}`));
        console.log(chalk.gray(`   markdown: ${mdOut}`));
        console.log(
          chalk.gray(
            `   rollback recommended: ${result.rollbackRecommended ? 'yes' : 'no'}`,
          ),
        );

        if (result.status === 'fail' && options.strict) {
          safeExit(1);
        }
      } catch (error: unknown) {
        console.error(chalk.red(`❌ release verify failed: ${toMessage(error)}`));
        safeExit(1);
      }
    });

  return command;
}
