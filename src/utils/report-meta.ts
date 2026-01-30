export type ReportMeta = {
  runId: string;
  createdAt: string;
  commitSha?: string;
  branch?: string;
  agent?: string;
  model?: string;
  traceId?: string;
};

type ReportMetaOptions = {
  createdAt?: string;
  runId?: string;
};

const envFirst = (keys: string[]): string | undefined => {
  for (const key of keys) {
    const value = process.env[key];
    if (value && value.trim()) {
      return value.trim();
    }
  }
  return undefined;
};

const parseDelimited = (value: string): string[] =>
  value
    .split(/[,\s]+/)
    .map((entry) => entry.trim())
    .filter(Boolean);

const resolveTraceId = (): string | undefined => {
  const direct = envFirst(['AE_TRACE_ID', 'TRACE_ID', 'REPORT_TRACE_ID']);
  if (direct) {
    return direct;
  }

  const list = envFirst(['REPORT_ENVELOPE_TRACE_IDS', 'TRACE_IDS']);
  if (!list) {
    return undefined;
  }

  const parsed = parseDelimited(list);
  return parsed.length > 0 ? parsed[0] : undefined;
};

export const buildReportMeta = (options: ReportMetaOptions = {}): ReportMeta => {
  const createdAt = options.createdAt ?? new Date().toISOString();
  const runId = options.runId
    ?? envFirst(['AE_RUN_ID', 'GITHUB_RUN_ID', 'CI_RUN_ID', 'RUN_ID'])
    ?? `local-${Date.now()}`;

  const commitSha = envFirst(['GITHUB_SHA', 'CI_COMMIT_SHA', 'GIT_COMMIT', 'COMMIT_SHA']);
  const branch = envFirst(['GITHUB_HEAD_REF', 'GITHUB_REF_NAME', 'GIT_BRANCH', 'CI_COMMIT_REF_NAME', 'BRANCH_NAME']);
  const agent = envFirst(['AE_AGENT_NAME', 'AGENT_NAME', 'AE_AGENT', 'AGENT']);
  const model = envFirst(['AE_MODEL', 'OPENAI_MODEL', 'ANTHROPIC_MODEL', 'GEMINI_MODEL', 'LLM_MODEL']);
  const traceId = resolveTraceId();

  return {
    runId,
    createdAt,
    ...(commitSha ? { commitSha } : {}),
    ...(branch ? { branch } : {}),
    ...(agent ? { agent } : {}),
    ...(model ? { model } : {}),
    ...(traceId ? { traceId } : {}),
  };
};
