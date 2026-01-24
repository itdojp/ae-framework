# Issue 1071: Codex SDK Evaluation (Draft)

## Snapshot
- Date: 2026-01-24
- Sources: OpenAI Codex SDK docs + GA announcement (see References)

## What the SDK provides (official)
- TypeScript SDK for programmatic Codex control
- Node.js 18+ required
- Install: `npm install @openai/codex-sdk`
- Basic flow: `startThread()` → `run()` → `resumeThread()`

## Relevance to ae-framework
- Replace Codex CLI subprocess orchestration with a TypeScript API
- Aligns with ae stage transitions: one thread per pipeline run or per stage
- Enables in-process result objects without stdout parsing

## Minimal PoC proposal
1) Select one stage (e.g., Formal → Tests) for SDK-only execution.
2) Create `CodexSdkClient` wrapper with:
   - thread lifecycle management
   - standardized prompt template
   - output normalization to existing artifact schema
3) Compare outputs and latency vs CLI run in a single sample scenario.

## Open questions
- Auth/credential handling for CI runners
- Thread persistence strategy (env var, artifact, or metadata store)
- Safe execution sandboxing for patch application

## References
- Codex SDK docs (developers.openai.com/codex/sdk)
- Codex GA announcement (openai.com/index/codex-now-generally-available)
