---
docRole: derived
canonicalSource:
- docs/product/ASSURANCE-CONTROL-PLANE.md
- docs/product/ASSURANCE-CONTROL-PLANE-POLICY.md
- docs/agents/agent-producer-matrix.md
- docs/reference/CONTRACT-CATALOG.md
lastVerified: '2026-06-05'
---

# Agent Evidence Adapters

> Language / 言語: English | 日本語

---

## English

Evidence adapters describe how raw producer output from coding agents and humans is routed into ae-framework judgment artifacts. They do not control agents, approve changes, or assert that an agent was correct. Their job is to collect enough contract-backed evidence for review, policy gates, handoff, and release decisions.

Use this document with:

- `docs/agents/agent-producer-matrix.md` for producer trust boundaries.
- `docs/reference/CONTRACT-CATALOG.md` for schema-backed artifact names and producer/consumer mapping.
- `docs/agents/handoff.md` for `ae-handoff/v1` continuation evidence.
- `docs/agents/hook-feedback.md` for `hook-feedback/v1` blockers and next actions.
- `docs/integrations/CODEX-INTEGRATION.md` and `docs/integrations/CODEX-ISSUE-RUNBOOK.md` for Codex CLI task input handling.

### Adapter boundary

An evidence adapter accepts raw producer output and emits or routes to existing ae-framework artifacts. It must preserve the distinction between producer assertions and control-plane judgment.

| Adapter concern | In scope | Out of scope |
| --- | --- | --- |
| Input | diff summaries, PR metadata, review comments, tool logs, command results, waiver notes | direct control of agent runtime, IDE, or hosted agent service |
| Normalization | map evidence to `change-package/v2`, `claim-evidence-manifest/v1`, `ae-handoff/v1`, `hook-feedback/v1`, and `policy-decision/v1` | invent a new guarantee level or bypass existing schema validation |
| Judgment | identify what evidence exists, what is missing, and what remains unresolved | mark agent output as correct only because an agent produced it |
| Enforcement | start report-only and feed policy gates when existing policy selects enforcement | add mandatory heavy tools for ordinary fast-lane changes |

### Producer examples and fixture mapping

The fixtures under `fixtures/agents/evidence-adapters/` are raw-output examples. They are intentionally not new contracts; each fixture records the expected existing artifacts an adapter would populate or request from existing generators.

| Producer | Fixture | Raw output captured | Primary normalized artifacts | Notes |
| --- | --- | --- | --- | --- |
| Codex CLI local task | `fixtures/agents/evidence-adapters/codex-output.json` | local diff summary, Issue source, validation commands, task conclusion | `change-package/v2`, `claim-evidence-manifest/v1`, `ae-handoff/v1`, `hook-feedback/v1` | Use `change-package:generate` for change scope, `claim-evidence:generate` when claims/evidence are present, and handoff/feedback builders for continuation state. |
| Claude Code task | `fixtures/agents/evidence-adapters/claude-code-output.json` | tool log summary, changed files, continuation notes | `ae-handoff/v1`, `hook-feedback/v1`, `change-package/v2`, optional `claim-evidence-manifest/v1` | Treat Claude Code as a producer; repository validation and review remain the control-plane evidence. |
| GitHub Copilot PR review/agent | `fixtures/agents/evidence-adapters/copilot-pr-output.json` | PR metadata, review body, inline comments, suggestions, thread state | `policy-decision/v1`, optional `change-package/v2`, optional `hook-feedback/v1` | Review thread state is source evidence. Unresolved AI review threads are blockers; resolved or non-actionable comments require a recorded disposition. |
| Human maintainer | `fixtures/agents/evidence-adapters/human-review-output.json` | approval, manual waiver decision, rationale, command evidence | `change-package/v2`, `policy-decision/v1`, `claim-evidence-manifest/v1` waiver entries | Human judgment can override policy only when owner, reason, expiry, affected claim, and evidence link are traceable. |

### Artifact selection rules

1. Use `change-package/v2` when the question is what changed, why it is reviewable, which claims are affected, and which evidence or waivers are attached.
2. Use `claim-evidence-manifest/v1` when the producer output mentions claims, tests, proofs, runtime mitigations, waivers, or unresolved gaps.
3. Use `ae-handoff/v1` when a future agent or human needs continuation context, blockers, completed steps, and next decisions.
4. Use `hook-feedback/v1` when the producer needs a compact response containing blockers, failed checks, missing inputs, or next actions.
5. Use `policy-decision/v1` when policy evaluation records pass, report-only, waived, or block decisions.
6. Keep raw logs as supporting evidence. The review surface should be the normalized summary artifact plus links to raw evidence.

### Minimum adapter workflow

For this Issue, the recommended implementation is documentation and fixtures only. A future script can read the fixture shape, but it must not become a new contract unless a schema and tests are added.

1. Capture producer output as JSON or Markdown in a local or CI artifact path.
2. Classify the producer and trust boundary using `docs/agents/agent-producer-matrix.md`.
3. Select the existing target artifacts from the table above.
4. Run the existing generators where applicable:
   - `pnpm run change-package:generate:v2`
   - `pnpm run claim-evidence:generate`
   - `node scripts/agents/create-handoff.mjs`
   - `node scripts/agents/build-hook-feedback.mjs`
5. Validate generated artifacts with the Contract Catalog's listed validators.
6. Record any missing command, unresolved claim, or waiver reason in the PR body and artifact summary.

### Non-goals

- Do not add a mandatory agent-output schema for raw producer logs in this slice.
- Do not require hosted agent APIs, external LLM calls, or network access.
- Do not promote `change-package/v2` from preview to production.
- Do not collapse `proved`, `model-checked`, `tested`, `runtime-mitigated`, `waived`, and `unresolved` into a single “passed” state.

---

## 日本語

Evidence adapter は、coding agent や人間の raw producer output を ae-framework の判断用 artifact へ接続する方針です。agent を制御したり、変更を承認したり、agent が正しいと主張したりするものではありません。目的は、review、policy gate、handoff、release decision に必要な contract-backed evidence を揃えることです。

併読資料:

- `docs/agents/agent-producer-matrix.md`: producer の trust boundary。
- `docs/reference/CONTRACT-CATALOG.md`: schema-backed artifact 名と producer/consumer mapping。
- `docs/agents/handoff.md`: `ae-handoff/v1` の continuation evidence。
- `docs/agents/hook-feedback.md`: `hook-feedback/v1` の blocker / next action。
- `docs/integrations/CODEX-INTEGRATION.md` / `docs/integrations/CODEX-ISSUE-RUNBOOK.md`: Codex CLI の task input handling。

### Adapter boundary

Evidence adapter は raw producer output を受け取り、既存 ae-framework artifact へ emit または routing します。producer assertion と control-plane judgment の区別を維持しなければなりません。

| Adapter concern | Scope に含む | Scope に含まない |
| --- | --- | --- |
| Input | diff summary、PR metadata、review comment、tool log、command result、waiver note | agent runtime、IDE、hosted agent service の直接制御 |
| Normalization | evidence を `change-package/v2`、`claim-evidence-manifest/v1`、`ae-handoff/v1`、`hook-feedback/v1`、`policy-decision/v1` へ接続する | 新しい保証レベルの発明、既存 schema validation の迂回 |
| Judgment | どの evidence があり、何が不足し、何が unresolved かを明示する | agent が出力したという理由だけで正しいと扱う |
| Enforcement | report-only から始め、既存 policy が enforcement を選んだ場合だけ policy gate に渡す | 通常の fast-lane 変更に重い tool を必須化する |

### Producer example と fixture mapping

`fixtures/agents/evidence-adapters/` 配下の fixture は raw output 例です。新しい contract ではありません。各 fixture は、adapter が populate する、または既存 generator へ要求する想定の existing artifact を記録します。

| Producer | Fixture | Captured raw output | 主な normalized artifact | Notes |
| --- | --- | --- | --- | --- |
| Codex CLI local task | `fixtures/agents/evidence-adapters/codex-output.json` | local diff summary、Issue source、validation command、task conclusion | `change-package/v2`, `claim-evidence-manifest/v1`, `ae-handoff/v1`, `hook-feedback/v1` | change scope は `change-package:generate`、claim/evidence がある場合は `claim-evidence:generate`、continuation state は handoff / feedback builder へ接続する。 |
| Claude Code task | `fixtures/agents/evidence-adapters/claude-code-output.json` | tool log summary、changed files、continuation note | `ae-handoff/v1`, `hook-feedback/v1`, `change-package/v2`, optional `claim-evidence-manifest/v1` | Claude Code は producer。repository validation と review が control-plane evidence に残る。 |
| GitHub Copilot PR review/agent | `fixtures/agents/evidence-adapters/copilot-pr-output.json` | PR metadata、review body、inline comment、suggestion、thread state | `policy-decision/v1`, optional `change-package/v2`, optional `hook-feedback/v1` | review thread state は source evidence。unresolved AI review thread は blocker。resolved または non-actionable comment には disposition を記録する。 |
| Human maintainer | `fixtures/agents/evidence-adapters/human-review-output.json` | approval、manual waiver decision、rationale、command evidence | `change-package/v2`, `policy-decision/v1`, `claim-evidence-manifest/v1` waiver entries | human judgment による policy override は owner、reason、expiry、affected claim、evidence link が traceable な場合だけ有効。 |

### Artifact selection rules

1. 何が変更され、なぜ review 可能で、どの claim が影響を受け、どの evidence / waiver が付くかを示す場合は `change-package/v2` を使います。
2. Producer output が claim、test、proof、runtime mitigation、waiver、unresolved gap に触れる場合は `claim-evidence-manifest/v1` を使います。
3. 将来の agent / human に continuation context、blocker、completed step、next decision を渡す場合は `ae-handoff/v1` を使います。
4. Producer に blocker、failed check、missing input、next action を compact に返す場合は `hook-feedback/v1` を使います。
5. Policy evaluation が pass、report-only、waived、block decision を記録する場合は `policy-decision/v1` を使います。
6. Raw log は supporting evidence に留めます。review surface は normalized summary artifact と raw evidence への link にします。

### Minimum adapter workflow

この Issue では、documentation + fixtures only を推奨します。将来 script が fixture shape を読むことはできますが、schema と test を追加するまでは新しい contract にしてはいけません。

1. Producer output を JSON または Markdown として local / CI artifact path に保存する。
2. `docs/agents/agent-producer-matrix.md` で producer と trust boundary を分類する。
3. 上の表から既存 target artifact を選ぶ。
4. 必要に応じて既存 generator を実行する。
   - `pnpm run change-package:generate:v2`
   - `pnpm run claim-evidence:generate`
   - `node scripts/agents/create-handoff.mjs`
   - `node scripts/agents/build-hook-feedback.mjs`
5. Contract Catalog に記載された validator で生成 artifact を検証する。
6. 未実行 command、unresolved claim、waiver reason は PR body と artifact summary に記録する。

### Non-goals

- この slice では raw producer log 用の mandatory schema を追加しません。
- hosted agent API、external LLM call、network access を要求しません。
- `change-package/v2` を preview から production へ昇格しません。
- `proved`、`model-checked`、`tested`、`runtime-mitigated`、`waived`、`unresolved` を単一の「passed」状態にまとめません。
