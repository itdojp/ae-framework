# Report Meta (Unified)

Adds a top-level `meta` to generated reports without breaking existing shapes.

Fields (always present):
- agent: { name, version }
- model: { provider, name }
- traceId: string|null
- iteration: number (default 0)
- runId: string|null
- commitSha: string|null (CI env or git rev-parse)
- branch: string|null (CI env or git rev-parse --abbrev-ref)
- environment: string (github|ci|value of AE_ENVIRONMENT|AE_QUALITY_PROFILE|NODE_ENV|local)
- createdAt: ISO string

Env sources (precedence):
- agent.name: AE_AGENT_NAME | AE_AGENT | AE_ACTOR | 'unknown'
- agent.version: AE_AGENT_VERSION | package.json version | null
- model.provider: AE_AGENT_MODEL_PROVIDER | (OPENAI→openai / ANTHROPIC→anthropic / GEMINI→google) | null
- model.name: AE_AGENT_MODEL | OPENAI_MODEL | ANTHROPIC_MODEL | GEMINI_MODEL | null
- traceId: TRACE_ID | AE_TRACE_ID | null
- iteration: AE_ITERATION | 0
- runId: RUN_ID | GITHUB_RUN_ID | CI_RUN_ID | CI_PIPELINE_ID | BUILD_BUILDID | CI_JOB_ID | null
- commitSha: GITHUB_SHA | CI_COMMIT_SHA | GIT_COMMIT | git rev-parse HEAD | null
- branch: GITHUB_REF_NAME | git rev-parse --abbrev-ref HEAD | null
- environment: AE_ENVIRONMENT | github (if GITHUB_ACTIONS) | ci (if CI) | AE_QUALITY_PROFILE | NODE_ENV | local

Examples:
```
{
  "meta": {
    "agent": { "name": "ae-framework", "version": "1.0.0" },
    "model": { "provider": "openai", "name": "gpt-4o-mini" },
    "traceId": null,
    "iteration": 0,
    "runId": "123456",
    "commitSha": "abcdef0123456789...",
    "branch": "feat/917-meta",
    "environment": "github",
    "createdAt": "2025-09-20T00:00:00.000Z"
  }
}
```

Implementation notes:
- Factory: `src/utils/meta-factory.ts` `buildReportMeta()`
- Integrated at save-time in `QualityGateRunner.saveReport()` so quality-gate reports automatically include meta.
- Other writers can adopt the same factory for consistency.

