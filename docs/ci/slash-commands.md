# Slash Commands Mapping (Issue #962)

Status: Draft (docs-only)
Scope: Command → labels/dispatch mapping used by agent-commands.yml.

Comment scope
- Commands are processed on PR comments (workflow `agent-commands.yml`). Issue-only commands are out of scope.

Core commands
- `/run-qa` → label `run-qa`
- `/run-security` → label `run-security`
- `/run-cedar` → label `run-cedar`
- `/non-blocking` → label `ci-non-blocking`
- `/blocking` → remove `ci-non-blocking`
- `/ready` → remove `do-not-merge` (alias: `/ready-for-review`)
- `/handoff A|B|C` → label `handoff:agent-a|b|c`

Coverage/perf/lighthouse
- `/coverage <pct|clear>` → set `coverage:<pct>` (clears existing coverage:*)
- `/enforce-coverage` → label `enforce-coverage`
- `/perf <pct|clear>` → set `perf:<pct>`
- `/enforce-perf` → label `enforce-perf`
- `/lh <pct|clear>` → set `lh:<pct>`
- `/enforce-lh` → label `enforce-lh`

Formal
- `/run-formal` → label `run-formal`
- `/enforce-formal` → label `enforce-formal`
- `/formal-help` `/formal-quickstart` → reply with quick tips/docs
- `/formal-aggregate-dispatch` → dispatch `formal-aggregate.yml` on PR head（Artifacts生成）。PRコメントのアップサートは `pull_request` 実行かつ `run-formal` ラベル時に行われます（idempotent, 固定ヘッダ `<!-- AE-FORMAL-AGGREGATE -->`）。
- `/formal-verify-dispatch` → dispatch `formal-verify.yml` on PR head (optional `inputs.target`)
- `/formal-apalache-dispatch` → dispatch `formal-verify.yml` with `inputs.target=apalache`

Security/SBOM
- `/run-security-dispatch` → dispatch `sbom-generation.yml` on PR head
- `/enforce-security` → label `enforce-security` (enforcement in cedar/sbom gates)

QA batches
- `/run-qa:commands` → label `qa-batch:commands`
- `/run-qa:cli` → label `qa-batch:cli`
- `/run-qa:property` → label `qa-batch:property`
- `/run-qa:agents` → label `qa-batch:agents`

Misc dispatchers
- `/verify-lite` → dispatch `verify-lite.yml` on PR head
- `/run-qa-dispatch` → dispatch `ae-ci.yml` on PR head
- `/ci-fast-dispatch` → dispatch `ci-fast.yml` on PR head
- `/run-flake-dispatch` → dispatch `flake-detect.yml` on PR head
- `/spec-validation-dispatch` → dispatch `spec-validation.yml` on PR head
- `/run-cedar-dispatch` → dispatch `cedar-quality-gates.yml` on PR head

Notes
- All comments from the bot include header `<!-- AE-AGENTS-REPLY -->` to reduce noise.
- See also: `docs/ci-policy.md`, `AGENTS.md`.
