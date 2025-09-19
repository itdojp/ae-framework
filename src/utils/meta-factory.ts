import { execSync } from 'node:child_process';
import { readFileSync } from 'node:fs';
import path from 'node:path';

export type ReportMeta = {
  agent: { name: string; version: string | null };
  model: { provider: string | null; name: string | null };
  traceId: string | null;
  iteration: number;
  runId: string | null;
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

function detectAgent(env: (k: string) => string | undefined): { name: string; version: string | null } {
  const name = env('AE_AGENT_NAME') || env('AE_AGENT') || env('AE_ACTOR') || 'unknown';
  let version: string | null = env('AE_AGENT_VERSION') || null;
  if (!version) {
    try {
      const pkgPath = path.join(process.cwd(), 'package.json');
      const pkg = JSON.parse(readFileSync(pkgPath, 'utf8')) as { version?: string };
      version = pkg?.version ?? null;
    } catch {
      version = null;
    }
  }
  return { name, version };
}

function detectModel(env: (k: string) => string | undefined): { provider: string | null; name: string | null } {
  const provider =
    (env('AE_AGENT_MODEL_PROVIDER') ||
      ((env('OPENAI_API_KEY') || env('OPENAI_MODEL')) ? 'openai' : undefined) ||
      ((env('ANTHROPIC_API_KEY') || env('ANTHROPIC_MODEL')) ? 'anthropic' : undefined) ||
      ((env('GEMINI_API_KEY') || env('GEMINI_MODEL')) ? 'google' : undefined)) ?? null;
  const name =
    env('AE_AGENT_MODEL') ||
    env('OPENAI_MODEL') ||
    env('ANTHROPIC_MODEL') ||
    env('GEMINI_MODEL') ||
    null;
  return { provider, name };
}

function detectEnvironment(env: (k: string) => string | undefined): string {
  if (env('AE_ENVIRONMENT')) return String(env('AE_ENVIRONMENT'));
  if (env('GITHUB_ACTIONS') === 'true') return 'github';
  if (env('CI')) return 'ci';
  return env('AE_QUALITY_PROFILE') || env('NODE_ENV') || 'local';
}

export function buildReportMeta(envOverride?: Record<string, string>): ReportMeta {
  const env = (k: string) => (envOverride && Object.prototype.hasOwnProperty.call(envOverride, k) ? envOverride[k] : process.env[k]);
  const createdAt = new Date().toISOString();
  const traceId = env('TRACE_ID') || env('AE_TRACE_ID') || null;
  const iterEnv = env('AE_ITERATION');
  const iteration = (() => {
    const n = iterEnv !== undefined ? Number(iterEnv) : 0;
    return Number.isFinite(n) ? n : 0;
  })();
  const runId = env('RUN_ID') || env('GITHUB_RUN_ID') || env('CI_RUN_ID') || env('CI_PIPELINE_ID') || env('BUILD_BUILDID') || env('CI_JOB_ID') || null;
  const commitSha = (env('GITHUB_SHA') || env('CI_COMMIT_SHA') || env('GIT_COMMIT')) || tryGit('git rev-parse HEAD');
  const branch = env('GITHUB_REF_NAME') || tryGit('git rev-parse --abbrev-ref HEAD');

  return {
    agent: detectAgent(env),
    model: detectModel(env),
    traceId,
    iteration,
    runId,
    commitSha: commitSha || null,
    branch: branch || null,
    environment: detectEnvironment(env),
    createdAt,
  };
}
