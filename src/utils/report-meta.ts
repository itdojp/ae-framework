import { execSync } from 'node:child_process';
import { readFileSync } from 'node:fs';
import path from 'node:path';

export type CommonReportMeta = {
  agent: { name: string; version?: string };
  model?: { provider?: string; name?: string };
  traceId?: string | null;
  iteration?: string | number | null;
  runId?: string | null;
  commitSha: string | null;
  branch: string | null;
  environment: string;
  createdAt: string;
};

function tryGit(cmd: string): string | null {
  try {
    const out = execSync(cmd, { stdio: ['ignore', 'pipe', 'ignore'] }).toString().trim();
    return out || null;
  } catch {
    return null;
  }
}

function detectAgent(): { name: string; version?: string } {
  const name = process.env['AE_AGENT'] || process.env['AE_AGENT_NAME'] || process.env['AE_ACTOR'] || 'ae-framework';
  let version: string | undefined;
  // Prefer explicit env, fallback to package.json version if readable
  version = process.env['AE_AGENT_VERSION'] || undefined;
  if (!version) {
    try {
      const pkgPath = path.join(process.cwd(), 'package.json');
      const pkg = JSON.parse(readFileSync(pkgPath, 'utf8')) as { version?: string };
      if (pkg?.version) version = pkg.version;
    } catch {
      // ignore
    }
  }
  return { name, ...(version ? { version } : {}) };
}

function detectModel(): { provider?: string; name?: string } | undefined {
  const provider =
    (process.env['OPENAI_API_KEY'] || process.env['OPENAI_MODEL']) ? 'openai' :
    (process.env['ANTHROPIC_API_KEY'] || process.env['ANTHROPIC_MODEL']) ? 'anthropic' :
    (process.env['GEMINI_API_KEY'] || process.env['GEMINI_MODEL']) ? 'google' :
    undefined;
  const name = process.env['OPENAI_MODEL'] || process.env['ANTHROPIC_MODEL'] || process.env['GEMINI_MODEL'] || undefined;
  if (!provider && !name) return undefined;
  return { ...(provider ? { provider } : {}), ...(name ? { name } : {}) };
}

function detectEnvironment(): string {
  if (process.env['GITHUB_ACTIONS'] === 'true') return 'github';
  if (process.env['CI']) return 'ci';
  return process.env['AE_QUALITY_PROFILE'] || process.env['NODE_ENV'] || 'local';
}

/** Build common meta object for report injection (non-breaking, additive). */
export function getCommonMeta(): CommonReportMeta {
  const createdAt = new Date().toISOString();
  const traceId = process.env['TRACE_ID'] || process.env['AE_TRACE_ID'] || null;
  const iteration = (process.env['AE_ITERATION'] ?? null) as string | number | null;
  const runId = process.env['GITHUB_RUN_ID'] || process.env['CI_RUN_ID'] || process.env['CI_PIPELINE_ID'] || process.env['BUILD_BUILDID'] || process.env['CI_JOB_ID'] || null;
  const commitSha = (process.env['GITHUB_SHA'] || process.env['CI_COMMIT_SHA'] || process.env['GIT_COMMIT']) || tryGit('git rev-parse HEAD');
  const branch = process.env['GITHUB_REF_NAME'] || tryGit('git rev-parse --abbrev-ref HEAD');

  return {
    agent: detectAgent(),
    ...(detectModel() ? { model: detectModel() } : {}),
    traceId,
    iteration,
    runId,
    commitSha: commitSha || null,
    branch: branch || null,
    environment: detectEnvironment(),
    createdAt,
  };
}
