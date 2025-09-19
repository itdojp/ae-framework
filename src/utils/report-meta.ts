import { execSync } from 'node:child_process';

export type CommonReportMeta = {
  agent: string | null;
  model: string | null;
  traceId: string | null;
  runId: string | null;
  commit: string | null;
};

function tryGitShortCommit(): string | null {
  try {
    const out = execSync('git rev-parse --short HEAD', { stdio: ['ignore', 'pipe', 'ignore'] })
      .toString()
      .trim();
    return out || null;
  } catch {
    return null;
  }
}

/**
 * Build common meta fields to inject into reports.
 * Source order is environment-first for portability; falls back to local git for commit.
 * Fields are nullable for backward compatibility.
 */
export function getCommonMeta(): CommonReportMeta {
  // Agent name (prefer explicit overrides)
  const agent =
    process.env['AE_AGENT'] ||
    process.env['AE_AGENT_NAME'] ||
    process.env['AE_ACTOR'] ||
    'ae-framework';

  // Model hints from common providers (best-effort)
  const model =
    process.env['OPENAI_MODEL'] ||
    process.env['ANTHROPIC_MODEL'] ||
    process.env['GEMINI_MODEL'] ||
    null;

  // Trace and run identifiers (CI-friendly)
  const traceId = process.env['TRACE_ID'] || process.env['AE_TRACE_ID'] || null;
  const runId =
    process.env['GITHUB_RUN_ID'] ||
    process.env['CI_RUN_ID'] ||
    process.env['CI_PIPELINE_ID'] ||
    process.env['BUILD_BUILDID'] ||
    process.env['CI_JOB_ID'] ||
    null;

  // Commit from CI if present, otherwise from local git
  const envSha = process.env['GITHUB_SHA'] || process.env['CI_COMMIT_SHA'] || process.env['GIT_COMMIT'];
  const commit = (envSha ? envSha.slice(0, 7) : null) || tryGitShortCommit();

  return { agent, model, traceId, runId, commit };
}

