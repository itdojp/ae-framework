import path from 'node:path';
import {
  resolveContainedWorkspacePath,
  resolveWorkspacePath,
  resolveWorkspaceRoot,
  toWorkspaceRelativePath,
  WorkspacePathPolicyError,
} from '../utils/workspace-path-policy.js';
import type { QualityGate } from './policy-loader.js';

export const QUALITY_GATE_EXECUTION_APPROVAL_SCOPE = 'quality-gate-execution' as const;
export const DEFAULT_QUALITY_ARTIFACT_ROOT = 'artifacts/quality' as const;
export const DEFAULT_QUALITY_REPORT_DIR = 'artifacts/quality/reports' as const;

export class QualityCommandPolicyError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'QualityCommandPolicyError';
  }
}

export interface QualityPathContext {
  workspaceRoot: string;
  artifactRoot: string;
}

export interface QualityPathContextOptions {
  workspaceRoot?: string;
  artifactRoot?: string;
}

export interface ResolvedQualityPath {
  resolvedPath: string;
  workspaceRelativePath: string;
}

export interface ApprovedQualityGateCommand {
  gateKey: string;
  executable: string;
  args: readonly string[];
  displayCommand: string;
  policyCommand: string;
  allowNonZeroExit?: boolean;
}

type ApprovedQualityGateCommandDefinition = Omit<ApprovedQualityGateCommand, 'gateKey'>;

const hasWindowsAbsolutePrefix = (value: string): boolean =>
  path.win32.isAbsolute(value) || /^[A-Za-z]:[\\/]/.test(value);

const isPathWithin = (baseDir: string, candidatePath: string): boolean => {
  const relative = path.relative(baseDir, candidatePath);
  return relative === '' || (!!relative && !relative.startsWith('..') && !path.isAbsolute(relative));
};

const normalizeWorkspaceRelativePath = (input: string, label: string): string => {
  const raw = String(input).trim();
  if (!raw) {
    throw new WorkspacePathPolicyError(`${label} must be a non-empty workspace-relative path`);
  }
  if (raw.includes('\0')) {
    throw new WorkspacePathPolicyError(`${label} must not contain NUL bytes`);
  }
  if (raw.includes('\\')) {
    throw new WorkspacePathPolicyError(`${label} must use POSIX-style '/' separators`);
  }
  if (raw.startsWith('//') || path.posix.isAbsolute(raw) || path.isAbsolute(raw) || hasWindowsAbsolutePrefix(raw)) {
    throw new WorkspacePathPolicyError(`${label} must be relative to the approved workspace`);
  }

  const segments = raw.split('/').filter(segment => segment !== '' && segment !== '.');
  if (segments.length === 0) {
    throw new WorkspacePathPolicyError(`${label} must be a non-empty workspace-relative path`);
  }
  if (segments.some(segment => segment === '..')) {
    throw new WorkspacePathPolicyError(`${label} must not contain parent-directory path components`);
  }

  return segments.join('/');
};

const normalizePolicyCommand = (command: string): string => command.trim().replace(/\s+/g, ' ');

const commandDefinitions = {
  accessibility: {
    executable: 'npm',
    args: ['run', 'test:a11y'],
    displayCommand: 'npm run test:a11y',
    policyCommand: 'npm run test:a11y',
  },
  coverage: {
    executable: 'npm',
    args: ['run', 'coverage'],
    displayCommand: 'npm run coverage',
    policyCommand: 'npm run coverage',
  },
  lighthouse: {
    executable: 'lhci',
    args: ['autorun'],
    displayCommand: 'lhci autorun (non-zero exit tolerated)',
    policyCommand: 'lhci autorun || true',
    allowNonZeroExit: true,
  },
  linting: {
    executable: 'node',
    args: ['scripts/quality/check-lint-summary.mjs'],
    displayCommand: 'node scripts/quality/check-lint-summary.mjs',
    policyCommand: 'node scripts/quality/check-lint-summary.mjs',
  },
  security: {
    executable: 'pnpm',
    args: ['audit', '--prod', '--json'],
    displayCommand: 'pnpm audit --prod --json',
    policyCommand: 'pnpm audit --prod --json',
  },
  tdd: {
    executable: 'node',
    args: ['scripts/quality/tdd-smoke-check.mjs'],
    displayCommand: 'node scripts/quality/tdd-smoke-check.mjs',
    policyCommand: 'node scripts/quality/tdd-smoke-check.mjs',
  },
  performance: {
    executable: 'npm',
    args: ['run', 'test:benchmarks'],
    displayCommand: 'npm run test:benchmarks',
    policyCommand: 'npm run test:benchmarks',
  },
  'api-validation': {
    executable: 'npm',
    args: ['run', 'validate:api'],
    displayCommand: 'npm run validate:api',
    policyCommand: 'npm run validate:api',
  },
} as const satisfies Record<string, ApprovedQualityGateCommandDefinition>;

export const APPROVED_QUALITY_GATE_COMMANDS: Readonly<Record<string, ApprovedQualityGateCommandDefinition>> = commandDefinitions;

export function getApprovedQualityGateCommand(gateKey: string, gate: QualityGate): ApprovedQualityGateCommand {
  const definition = APPROVED_QUALITY_GATE_COMMANDS[gateKey];
  if (!definition) {
    throw new QualityCommandPolicyError(
      `Quality gate '${gateKey}' does not have a code-owned command allowlist entry`
    );
  }

  const policyCommand = normalizePolicyCommand(gate.commands.test);
  const expectedPolicyCommand = normalizePolicyCommand(definition.policyCommand);
  if (policyCommand !== expectedPolicyCommand) {
    throw new QualityCommandPolicyError(
      `Quality gate '${gateKey}' policy command is not trusted; expected '${definition.policyCommand}'`
    );
  }

  const command: ApprovedQualityGateCommand = {
    gateKey,
    executable: definition.executable,
    args: [...definition.args],
    displayCommand: definition.displayCommand,
    policyCommand: definition.policyCommand,
  };
  if (definition.allowNonZeroExit === true) {
    command.allowNonZeroExit = true;
  }
  return command;
}

export function createQualityPathContext(options: QualityPathContextOptions = {}): QualityPathContext {
  const workspaceRoot = resolveWorkspaceRoot({ defaultRoot: options.workspaceRoot ?? process.cwd() });
  const artifactRootInput = options.artifactRoot ?? process.env['AE_QUALITY_ARTIFACT_ROOT'] ?? DEFAULT_QUALITY_ARTIFACT_ROOT;
  const artifactRoot = resolveWorkspacePath(
    normalizeWorkspaceRelativePath(artifactRootInput, 'quality artifact root'),
    { workspaceRoot, label: 'quality artifact root' }
  );
  return { workspaceRoot, artifactRoot };
}

export function getDefaultQualityReportDir(context: QualityPathContext): string {
  const artifactRoot = toWorkspaceRelativePath(context.artifactRoot, {
    workspaceRoot: context.workspaceRoot,
    label: 'quality artifact root',
  });
  return path.posix.join(artifactRoot, 'reports');
}

export function resolveQualityReportOutputDir(
  input: string,
  context: QualityPathContext,
  label = 'quality report output directory'
): ResolvedQualityPath {
  if (path.isAbsolute(input) || hasWindowsAbsolutePrefix(input)) {
    throw new WorkspacePathPolicyError(`${label} must be relative to the approved quality artifact root`);
  }

  const workspaceRelative = normalizeWorkspaceRelativePath(input, label);
  let resolvedPath = resolveWorkspacePath(workspaceRelative, {
    workspaceRoot: context.workspaceRoot,
    label,
  });

  if (!isPathWithin(context.artifactRoot, resolvedPath)) {
    throw new WorkspacePathPolicyError(`${label} must stay under the approved quality artifact root`);
  }

  const artifactRelative = path.relative(context.artifactRoot, resolvedPath).replace(/\\/g, '/');
  if (artifactRelative !== '') {
    resolvedPath = resolveContainedWorkspacePath(context.artifactRoot, artifactRelative, label);
  }

  return {
    resolvedPath,
    workspaceRelativePath: toWorkspaceRelativePath(resolvedPath, {
      workspaceRoot: context.workspaceRoot,
      label,
    }),
  };
}

export function resolveQualityWorkspacePath(
  input: string,
  context: QualityPathContext,
  label = 'quality workspace path'
): ResolvedQualityPath {
  const resolvedPath = resolveWorkspacePath(input, {
    workspaceRoot: context.workspaceRoot,
    label,
  });

  return {
    resolvedPath,
    workspaceRelativePath: toWorkspaceRelativePath(resolvedPath, {
      workspaceRoot: context.workspaceRoot,
      label,
    }),
  };
}

const isTruthyFlag = (value: string | undefined): boolean => {
  if (!value) return false;
  return ['1', 'true', 'yes', 'y'].includes(value.trim().toLowerCase());
};

export function isQualityAgentContext(): boolean {
  const raw = process.env['AE_QUALITY_AGENT_CONTEXT'] ?? process.env['AE_AGENT_CONTEXT'];
  return isTruthyFlag(raw);
}

export function isQualityCiContext(): boolean {
  return isTruthyFlag(process.env['CI']);
}
