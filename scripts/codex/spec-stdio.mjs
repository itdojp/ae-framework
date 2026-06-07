#!/usr/bin/env node
// CodeX stdio bridge (no MCP): AE-Spec compile/validate/codegen tools
// Input: single-line JSON { action: 'compile|validate|codegen', args: {...} }
// Output: single-line JSON result { ok: boolean, data?: any, error?: string }

import fs from 'node:fs';
import path from 'node:path';
import { pathToFileURL } from 'node:url';

const DEFAULT_ARTIFACT_ROOT = 'artifacts/spec-synthesis';
const CODEGEN_MATERIALIZE_APPROVAL_SCOPE = 'high-impact:codegen-materialize';
const CODEGEN_TARGETS = new Set(['typescript', 'api', 'database', 'react']);
const TRUSTED_TRUE_VALUES = new Set(['1', 'true', 'yes', 'on', 'TRUE', 'YES', 'ON', 'True', 'Yes', 'On']);

class SpecStdioPolicyError extends Error {
  constructor(message) {
    super(message);
    this.name = 'SpecStdioPolicyError';
  }
}

function respond(obj) {
  process.stdout.write(JSON.stringify(obj) + '\n');
}

function respondError(error, exitCode = 1) {
  process.exitCode = exitCode;
  respond({ ok: false, error });
}

const isTrustedTrue = (value) => TRUSTED_TRUE_VALUES.has(String(value || '').trim());

const hasWindowsAbsolutePrefix = (value) => path.win32.isAbsolute(value) || /^[A-Za-z]:[\\/]/.test(value);

const isPathWithin = (baseDir, candidatePath) => {
  const relative = path.relative(baseDir, candidatePath);
  return relative === '' || (!!relative && !relative.startsWith('..') && !path.isAbsolute(relative));
};

const splitInputPath = (value) => value.replace(/\\/g, '/').split('/');

const nearestExistingAncestor = (resolvedPath) => {
  let current = path.resolve(resolvedPath);
  while (!fs.existsSync(current)) {
    const parent = path.dirname(current);
    if (parent === current) return null;
    current = parent;
  }
  return current;
};

const safeRealpathSync = (value, label) => {
  try {
    return fs.realpathSync(value);
  } catch {
    throw new SpecStdioPolicyError(`${label} could not be resolved safely`);
  }
};

const assertExistingAncestorWithin = (workspaceRoot, resolvedPath, label) => {
  if (!fs.existsSync(workspaceRoot)) return;
  const ancestor = nearestExistingAncestor(resolvedPath);
  if (!ancestor) return;

  const realRoot = safeRealpathSync(workspaceRoot, label);
  const realAncestor = safeRealpathSync(ancestor, label);
  if (!isPathWithin(realRoot, realAncestor)) {
    throw new SpecStdioPolicyError(`${label} resolves through a filesystem entry outside the approved workspace`);
  }
};

const resolveSpecWorkspaceRoot = () => {
  const fromEnv = [
    process.env.AE_CODEX_SPEC_STDIO_WORKSPACE_ROOT,
    process.env.AE_MCP_WORKSPACE_ROOT,
    process.env.AE_WORKSPACE_ROOT,
  ].map((value) => String(value || '').trim()).find(Boolean);
  return path.resolve(fromEnv || process.cwd());
};

const resolveWorkspacePath = (input, { workspaceRoot, label }) => {
  const raw = String(input || '').trim();
  if (!raw) {
    throw new SpecStdioPolicyError(`${label} must be a non-empty workspace-relative path`);
  }
  if (raw.includes('\0')) {
    throw new SpecStdioPolicyError(`${label} must not contain NUL bytes`);
  }
  if (raw.includes('\\')) {
    throw new SpecStdioPolicyError(`${label} must use POSIX-style '/' separators`);
  }
  if (raw.startsWith('//') || path.isAbsolute(raw) || hasWindowsAbsolutePrefix(raw)) {
    throw new SpecStdioPolicyError(`${label} must be relative to the approved workspace`);
  }

  const segments = splitInputPath(raw);
  if (segments.some((segment) => segment === '.' || segment === '..')) {
    throw new SpecStdioPolicyError(`${label} must not contain dot-segment path components`);
  }
  if (segments.some((segment) => segment.toLowerCase() === '.git')) {
    throw new SpecStdioPolicyError(`${label} must not target Git metadata directories`);
  }

  const root = path.resolve(workspaceRoot);
  const resolved = path.resolve(root, raw);
  if (!isPathWithin(root, resolved)) {
    throw new SpecStdioPolicyError(`${label} escaped the approved workspace`);
  }
  assertExistingAncestorWithin(root, resolved, label);
  return resolved;
};

const toWorkspaceRelativePath = (resolvedPath, workspaceRoot, label) => {
  const root = path.resolve(workspaceRoot);
  const absolutePath = path.resolve(resolvedPath);
  if (!isPathWithin(root, absolutePath)) {
    throw new SpecStdioPolicyError(`${label} is outside the approved workspace`);
  }
  const relative = path.relative(root, absolutePath);
  return relative === '' ? '.' : relative.replace(/\\/g, '/');
};

const resolveArtifactRoot = (workspaceRoot) => resolveWorkspacePath(
  process.env.AE_CODEX_SPEC_STDIO_ARTIFACT_ROOT || DEFAULT_ARTIFACT_ROOT,
  {
    workspaceRoot,
    label: 'codex:spec:stdio artifact root',
  },
);

const allowWorkspaceWrites = () => isTrustedTrue(process.env.AE_CODEX_SPEC_STDIO_ALLOW_WORKSPACE_WRITES);

const resolveOutputPath = (input, { workspaceRoot, artifactRoot, label }) => {
  const resolved = resolveWorkspacePath(input, { workspaceRoot, label });
  if (!allowWorkspaceWrites() && !isPathWithin(path.resolve(artifactRoot), resolved)) {
    const artifactRootArg = toWorkspaceRelativePath(artifactRoot, workspaceRoot, 'codex:spec:stdio artifact root');
    throw new SpecStdioPolicyError(`${label} must stay under the approved artifact root (${artifactRootArg})`);
  }
  return resolved;
};

const approvalScopes = (approval) => {
  if (!approval || typeof approval !== 'object' || Array.isArray(approval)) return [];
  const values = [];
  if (typeof approval.scope === 'string') values.push(approval.scope);
  if (Array.isArray(approval.scopes)) {
    for (const scope of approval.scopes) {
      if (typeof scope === 'string') values.push(scope);
    }
  }
  return values.map((scope) => scope.trim()).filter(Boolean);
};

const hasRequestApprovalScope = (req, requiredScope) => {
  const approval = req.approval || req.args?.approval;
  if (!approval || typeof approval !== 'object' || Array.isArray(approval)) return false;
  if (approval.approved !== true) return false;
  const scopes = new Set(approvalScopes(approval));
  return (
    scopes.has(requiredScope) ||
    scopes.has('codex-spec-stdio') ||
    scopes.has('codex-spec-stdio:*') ||
    scopes.has('codex-spec-stdio-all')
  );
};

const hasTrustedApproval = (req, requiredScope) => {
  if (isTrustedTrue(process.env.AE_CODEX_SPEC_STDIO_TRUSTED_CONTEXT)) {
    return true;
  }
  return (
    isTrustedTrue(process.env.AE_CODEX_SPEC_STDIO_TRUSTED_APPROVAL) &&
    hasRequestApprovalScope(req, requiredScope)
  );
};

const requireTrustedApproval = (req, requiredScope, reason) => {
  if (hasTrustedApproval(req, requiredScope)) return;
  throw new SpecStdioPolicyError(
    `${reason} requires trusted approval (${requiredScope}); set AE_CODEX_SPEC_STDIO_TRUSTED_CONTEXT=1 for a trusted runner or set AE_CODEX_SPEC_STDIO_TRUSTED_APPROVAL=1 and include approval.approved=true with the required scope`,
  );
};

const resolveCompilePaths = (args) => {
  const workspaceRoot = resolveSpecWorkspaceRoot();
  const artifactRoot = resolveArtifactRoot(workspaceRoot);
  const inputPath = resolveWorkspacePath(args.inputPath, {
    workspaceRoot,
    label: 'codex:spec:stdio compile inputPath',
  });
  const outputPath = args.outputPath
    ? resolveOutputPath(args.outputPath, {
      workspaceRoot,
      artifactRoot,
      label: 'codex:spec:stdio compile outputPath',
    })
    : undefined;
  return { workspaceRoot, artifactRoot, inputPath, outputPath };
};

const resolveValidateInputPath = (args) => {
  const workspaceRoot = resolveSpecWorkspaceRoot();
  const inputPath = resolveWorkspacePath(args.inputPath, {
    workspaceRoot,
    label: 'codex:spec:stdio validate inputPath',
  });
  return { workspaceRoot, inputPath };
};

const normalizeTargets = (targets) => {
  const requested = Array.isArray(targets) && targets.length ? targets : ['typescript', 'api', 'database'];
  const normalized = [];
  for (const target of requested) {
    const value = String(target || '').trim();
    if (!CODEGEN_TARGETS.has(value)) {
      throw new SpecStdioPolicyError(`codex:spec:stdio codegen target is not allowed: ${value || '(empty)'}`);
    }
    if (!normalized.includes(value)) normalized.push(value);
  }
  return normalized;
};

const resolveContainedOutputPath = (baseDir, relativePath, label) => {
  const resolved = resolveWorkspacePath(relativePath, { workspaceRoot: baseDir, label });
  if (!isPathWithin(path.resolve(baseDir), resolved)) {
    throw new SpecStdioPolicyError(`${label} escaped the approved output directory`);
  }
  return resolved;
};

const resolveCodegenPaths = (args) => {
  const workspaceRoot = resolveSpecWorkspaceRoot();
  const artifactRoot = resolveArtifactRoot(workspaceRoot);
  const artifactRootArg = toWorkspaceRelativePath(artifactRoot, workspaceRoot, 'codex:spec:stdio artifact root');
  const irPath = resolveWorkspacePath(args.irPath || `${artifactRootArg}/ae-ir.json`, {
    workspaceRoot,
    label: 'codex:spec:stdio codegen irPath',
  });
  const irPathArg = toWorkspaceRelativePath(irPath, workspaceRoot, 'codex:spec:stdio codegen irPath');
  const outBase = resolveOutputPath(args.outDir || `${artifactRootArg}/generated`, {
    workspaceRoot,
    artifactRoot,
    label: 'codex:spec:stdio codegen outDir',
  });
  const outBaseArg = toWorkspaceRelativePath(outBase, workspaceRoot, 'codex:spec:stdio codegen outDir');
  const targets = normalizeTargets(args.targets);
  const targetOutDirs = {};
  const targetOutDirArgs = {};
  for (const target of targets) {
    const targetDir = resolveContainedOutputPath(outBase, target, `codex:spec:stdio codegen ${target} outDir`);
    targetOutDirs[target] = targetDir;
    targetOutDirArgs[target] = toWorkspaceRelativePath(targetDir, workspaceRoot, `codex:spec:stdio codegen ${target} outDir`);
  }
  return { workspaceRoot, artifactRoot, irPath, irPathArg, outBase, outBaseArg, targets, targetOutDirs, targetOutDirArgs };
};

const createCodegenChildProcessOptions = (workspaceRoot) => ({
  stdio: 'inherit',
  cwd: workspaceRoot,
  env: {
    ...process.env,
    AE_CODEGEN_WORKSPACE_ROOT: workspaceRoot,
  },
});

const buildCodegenCliArgs = (paths, target, dir) => [
  'dist/src/cli/index.js',
  'codegen',
  'generate',
  '-i',
  paths.irPathArg,
  '-o',
  dir,
  '-t',
  target,
  '--apply',
  '--approval-scope',
  CODEGEN_MATERIALIZE_APPROVAL_SCOPE,
];

async function loadSpecCompiler(req, workspaceRoot) {
  const importErrors = [];
  try {
    return await import('@ae-framework/spec-compiler');
  } catch (error) {
    importErrors.push(error instanceof Error ? error.message : String(error));
  }

  const localDist = path.resolve(workspaceRoot, 'packages/spec-compiler/dist/index.js');
  if (!fs.existsSync(localDist)) {
    try {
      const { spawnSync } = await import('child_process');
      requireTrustedApproval(req, 'codex-spec-stdio-build', 'Spec compiler auto-build');
      const build = spawnSync('pnpm', ['-s', '--filter', '@ae-framework/spec-compiler', 'build'], {
        cwd: workspaceRoot,
        encoding: 'utf8',
      });
      if (build.status !== 0) {
        importErrors.push(`pnpm build failed: ${(build.stderr || build.stdout || '').trim()}`);
      }
    } catch (error) {
      importErrors.push(`failed to run pnpm build: ${error instanceof Error ? error.message : String(error)}`);
    }
  }

  if (fs.existsSync(localDist)) {
    try {
      return await import(pathToFileURL(localDist).href);
    } catch (error) {
      importErrors.push(error instanceof Error ? error.message : String(error));
    }
  }

  throw new Error(`Unable to load @ae-framework/spec-compiler (${importErrors.join(' | ')})`);
}

async function main() {
  try {
    const input = await new Promise((resolve, reject) => {
      let buf = '';
      process.stdin.setEncoding('utf8');
      process.stdin.on('data', (d) => (buf += d));
      process.stdin.on('end', () => resolve(buf));
      process.stdin.on('error', reject);
    });
    const line = input.trim().split('\n').filter(Boolean).pop() || '{}';
    let req;
    try {
      req = JSON.parse(line);
    } catch (error) {
      const message = error instanceof Error ? error.message : String(error);
      return respondError(`Invalid JSON input: ${message}`, 2);
    }
    const action = req.action;
    const args = req.args || {};

    if (!action) return respondError('Missing action', 2);

    switch (action) {
      case 'compile': {
        const paths = resolveCompilePaths(args);
        if (paths.outputPath) {
          requireTrustedApproval(req, 'codex-spec-stdio-compile-write', 'AE-IR output writes');
          fs.mkdirSync(path.dirname(paths.outputPath), { recursive: true });
        }
        const { AESpecCompiler } = await loadSpecCompiler(req, paths.workspaceRoot);
        const compiler = new AESpecCompiler();
        const prev = process.env.AE_SPEC_RELAXED;
        if (args.relaxed) process.env.AE_SPEC_RELAXED = '1';
        try {
          const ir = await compiler.compile({
            inputPath: paths.inputPath,
            outputPath: paths.outputPath,
            validate: args.validate !== false,
          });
          const lint = await compiler.lint(ir);
          return respond({ ok: true, data: {
            outputPath: paths.outputPath
              ? toWorkspaceRelativePath(paths.outputPath, paths.workspaceRoot, 'codex:spec:stdio compile outputPath')
              : null,
            summary: lint.summary,
            counts: { entities: ir.domain.length, apis: ir.api.length, usecases: ir.usecases.length },
          }});
        } finally {
          process.env.AE_SPEC_RELAXED = prev;
        }
      }
      case 'validate': {
        const paths = resolveValidateInputPath(args);
        const { AESpecCompiler } = await loadSpecCompiler(req, paths.workspaceRoot);
        const compiler = new AESpecCompiler();
        const prev = process.env.AE_SPEC_RELAXED;
        if (args.relaxed) process.env.AE_SPEC_RELAXED = '1';
        try {
          const ir = await compiler.compile({ inputPath: paths.inputPath, validate: false });
          const lint = await compiler.lint(ir);
          const issues = lint.issues.slice(0, 100).map(i => ({ severity: i.severity, id: i.id, message: i.message, section: i.location?.section || 'root' }));
          const passed = lint.summary.errors === 0 && (args.maxWarnings == null || lint.summary.warnings <= args.maxWarnings);
          return respond({ ok: true, data: { passed, summary: lint.summary, issues } });
        } finally {
          process.env.AE_SPEC_RELAXED = prev;
        }
      }
      case 'codegen': {
        const { spawnSync } = await import('child_process');
        const paths = resolveCodegenPaths(args);
        requireTrustedApproval(req, 'codex-spec-stdio-codegen', 'Code generation child process and filesystem writes');
        const run = (t, dir) => spawnSync(
          process.execPath,
          buildCodegenCliArgs(paths, t, dir),
          createCodegenChildProcessOptions(paths.workspaceRoot),
        );
        const results = {};
        const failedTargets = [];
        for (const t of paths.targets) {
          const dir = paths.targetOutDirArgs[t];
          const runResult = run(t, dir);
          if (runResult.error) {
            return respondError(`Codegen failed for target ${t}: ${runResult.error.message}`);
          }
          if (runResult.status !== 0) {
            failedTargets.push(t);
          }
          results[t] = dir;
        }
        if (failedTargets.length > 0) {
          return respondError(`Codegen failed for targets: ${failedTargets.join(', ')}`);
        }
        return respond({ ok: true, data: { outBase: paths.outBaseArg, results } });
      }
      default:
        return respondError(`Unknown action: ${action}`, 2);
    }
  } catch (err) {
    respondError(err instanceof Error ? err.message : String(err));
  }
}

main();
