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

function detectAgent(): { name: string; version: string | null } {
  const name = process.env['AE_AGENT_NAME'] || process.env['AE_AGENT'] || process.env['AE_ACTOR'] || 'unknown';
  let version: string | null = process.env['AE_AGENT_VERSION'] || null;
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

function detectModel(): { provider: string | null; name: string | null } {
  const provider =
    (process.env['AE_AGENT_MODEL_PROVIDER'] ||
      ((process.env['OPENAI_API_KEY'] || process.env['OPENAI_MODEL']) ? 'openai' : undefined) ||
      ((process.env['ANTHROPIC_API_KEY'] || process.env['ANTHROPIC_MODEL']) ? 'anthropic' : undefined) ||
      ((process.env['GEMINI_API_KEY'] || process.env['GEMINI_MODEL']) ? 'google' : undefined)) ?? null;
  const name =
    process.env['AE_AGENT_MODEL'] ||
    process.env['OPENAI_MODEL'] ||
    process.env['ANTHROPIC_MODEL'] ||
    process.env['GEMINI_MODEL'] ||
    null;
  return { provider, name };
}

function detectEnvironment(): string {
  if (process.env['AE_ENVIRONMENT']) return String(process.env['AE_ENVIRONMENT']);
  if (process.env['GITHUB_ACTIONS'] === 'true') return 'github';
  if (process.env['CI']) return 'ci';
  return process.env['AE_QUALITY_PROFILE'] || process.env['NODE_ENV'] || 'local';
}

export function buildReportMeta(): ReportMeta {
  const createdAt = new Date().toISOString();
  const traceId = process.env['TRACE_ID'] || process.env['AE_TRACE_ID'] || null;
  const iterEnv = process.env['AE_ITERATION'];
  const iteration = (() => {
    const n = iterEnv !== undefined ? Number(iterEnv) : 0;
    return Number.isFinite(n) ? n : 0;
  })();
  const runId = process.env['RUN_ID'] || process.env['GITHUB_RUN_ID'] || process.env['CI_RUN_ID'] || process.env['CI_PIPELINE_ID'] || process.env['BUILD_BUILDID'] || process.env['CI_JOB_ID'] || null;
  const commitSha = (process.env['GITHUB_SHA'] || process.env['CI_COMMIT_SHA'] || process.env['GIT_COMMIT']) || tryGit('git rev-parse HEAD');
  const branch = process.env['GITHUB_REF_NAME'] || tryGit('git rev-parse --abbrev-ref HEAD');

  return {
    agent: detectAgent(),
    model: detectModel(),
    traceId,
    iteration,
    runId,
    commitSha: commitSha || null,
    branch: branch || null,
    environment: detectEnvironment(),
    createdAt,
  };
}

