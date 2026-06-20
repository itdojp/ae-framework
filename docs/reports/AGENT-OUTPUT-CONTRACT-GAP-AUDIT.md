---
docRole: derived
canonicalSource:
  - docs/product/ASSURANCE-CONTROL-PLANE-POLICY.md
  - docs/reference/CONTRACT-CATALOG.md
  - docs/agents/agent-producer-matrix.md
  - docs/agents/evidence-adapters.md
lastVerified: '2026-06-20'
---

# Agent Output Contract Gap Audit

> Language / 言語: English | 日本語

---

## English

### 1. Purpose and scope

This report audits how replaceable producers feed the ae-framework assurance control plane without turning raw producer output into a release judgment. It is the gap register for the ACP-010 slice and gives later ACP issues stable gap IDs.

The audit scope is documentation and contract routing only. It does not introduce a new production schema, adapter script, policy gate block condition, CLI, or MCP server.

### 2. Routing inventory

| Producer class | Raw signal | Normalized judgment artifact | Schema / validator | Primary consumer | Enforcement default | Gap IDs |
| --- | --- | --- | --- | --- | --- | --- |
| Codex CLI local task | local diff summary, Issue source, validation commands, task conclusion | `change-package/v2`, `claim-evidence-manifest/v1`, `ae-handoff/v1`, `hook-feedback/v1` | `schema/change-package-v2.schema.json`, `schema/claim-evidence-manifest.schema.json`, `schema/ae-handoff.schema.json`, `schema/hook-feedback.schema.json`; validators listed in the Contract Catalog | PR reviewer, `policy-gate`, PR summary, continuation handoff | report-only unless required checks, risk policy, or explicit assurance profile selects enforcement | ACP-GAP-001, ACP-GAP-002 |
| Claude Code task | tool log summary, changed files, continuation notes, command evidence | `ae-handoff/v1`, `hook-feedback/v1`, `change-package/v2`, optional `claim-evidence-manifest/v1` | `schema/ae-handoff.schema.json`, `schema/hook-feedback.schema.json`, `schema/change-package-v2.schema.json`, optional manifest validation | main agent, reviewer, continuation consumer | report-only; repository validation remains authoritative | ACP-GAP-001, ACP-GAP-002 |
| GitHub Copilot PR review / agent | review body, inline comments, suggestions, thread state, PR diff | PR review records, `policy-decision/v1`, optional `change-package/v2`, optional `hook-feedback/v1` | `pr-review-completeness` script for review-thread integrity; `schema/policy-decision-v1.schema.json` when policy records a decision | Copilot Review Gate, reviewer, `policy-gate`, PR summary | unresolved AI review threads can block; generated review text is not judgment by itself | ACP-GAP-001, ACP-GAP-003, ACP-GAP-004 |
| Human maintainer | approval, rationale, manual waiver, merge decision, command evidence | `temporary-override/v1`, `policy-decision/v1`, `claim-evidence-manifest/v1`, `change-package/v2`, PR review record | `schema/temporary-override-v1.schema.json`, `schema/policy-decision-v1.schema.json`, `schema/claim-evidence-manifest.schema.json`, reviewer policy / branch protection | `policy-gate`, release reviewer, audit trail | only traceable waiver metadata can override; unresolved risk stays visible | ACP-GAP-001 |
| CI / test runner | required-check status, logs, coverage, quality scorecard, harness health, provenance | `verify-lite-run-summary`, `quality-scorecard`, `harness-health`, `policy-input-v1`, `policy-decision/v1`, provenance sidecars | `schema/verify-lite-run-summary.schema.json`, `schema/quality-scorecard.schema.json`, `schema/harness-health.schema.json`, `schema/policy-input-v1.schema.json`, `schema/ci-artifact-provenance-v1.schema.json` | branch protection, PR comments, policy gate, release summary | required checks enforce; side summaries stay report-only unless existing policy escalates | ACP-GAP-003, ACP-GAP-005 |
| Formal runner / model checker / proof tool | model/proof result, counterexample, scope, assumptions | `formal-summary/v2`, compatibility `formal-summary/v1`, `assurance-summary/v1`, `claim-evidence-manifest/v1`, optional `change-package/v2` | `schema/formal-summary-v2.schema.json`, `schema/formal-summary-v1.schema.json`, `schema/assurance-summary.schema.json`, manifest validation | assurance summary, PR summary, release reviewer | supports only the scoped claim; not mandatory for routine PRs | ACP-GAP-003 |
| MCP tool server | TaskResponse JSON, generated spec/test/code snippets, blocked/next-action response | `TaskResponse`, `ae-handoff/v1`, `hook-feedback/v1`, downstream `change-package/v2` when files change | `schema/codex-task-response.schema.json`, path/approval policy tests, generated-artifact validation | caller, continuation consumer, main-agent reviewer | invalid tool output is rejected; successful tool output remains producer input until reviewed | ACP-GAP-002, ACP-GAP-006 |
| Other BYO coding agents, including Gemini-family tools | diff, comments, command transcript, tool-specific raw log | same existing artifacts selected by output type, not by vendor | existing artifact schemas; no vendor-specific raw API schema in this slice | reviewer and policy surface through the normalized artifact | report-only until mapped through an existing artifact and risk policy | ACP-GAP-006 |

### 3. Gap register

| Gap ID | Category | Current state | Decision / next owner | Follow-up |
| --- | --- | --- | --- | --- |
| ACP-GAP-001 | missing fixture | `fixtures/agents/evidence-adapters/` has representative raw examples, but no audited fixture-set manifest that states required producers, negative cases, and expected normalized artifacts for the ACP rollout. | Add a bounded fixture set; keep fixtures examples, not production contracts. | ACP-011 / #3482 |
| ACP-GAP-002 | intentional preview / missing adapter | The docs select existing artifacts, but no report-only normalizer skeleton consumes raw producer examples and emits artifact-routing requests. | Add a non-enforcing skeleton that refuses to invent new claim states or schemas. | ACP-012 / #3483 |
| ACP-GAP-003 | missing docs / reviewer surface | Existing summaries are spread across verify-lite, quality scorecard, formal, assurance, and PR comments; producer-output gap status is not consolidated for reviewers. | Surface gap IDs and missing evidence in the Assurance Summary PR view without adding a mandatory heavy lane. | ACP-030 / #3486 |
| ACP-GAP-004 | missing policy integration | Policy Gate already records decisions and AI review gates check unresolved threads, but normalized agent-assurance findings are not yet consumed as report-only policy context. | Feed report-only findings into policy input/decision while keeping enforcement opt-in. | ACP-040 / #3488 |
| ACP-GAP-005 | missing validator / contract treatment | Some CI sidecars remain listed as dedicated-schema gaps in the Contract Catalog, for example `policy-shadow-compare.v1` and selected `artifacts/ci/*-summary.json` patterns. | Keep as cataloged contract debt; do not block ACP producer routing unless a later issue scopes the sidecar. | Existing Contract Catalog gap list |
| ACP-GAP-006 | out of scope | Vendor-specific raw APIs for future or external agents are not part of the control-plane contract. | Normalize by output type through existing artifacts; avoid vendor-specific runtime coupling. | Documented non-goal |

### 4. Operating rules

1. Producer output is raw input to judgment, not a judgment artifact by itself.
2. Use the existing artifact selected by evidence type: change package for changed scope, manifest for claims, handoff for continuation, hook feedback for blockers, policy decision for pass/report-only/waived/block state.
3. New producer lanes start report-only unless risk labels, `enforce-assurance`, or critical-core policy explicitly select enforcement.
4. Do not add a mandatory raw-agent-output schema in this slice. ACP-GAP-001 fixtures remain examples until a later schema issue explicitly changes that decision.
5. If Context Pack or Boundary Map conflicts with a producer diff, stop and resolve the design conflict before treating the output as reviewable.

---

## 日本語

### 1. 目的と範囲

この report は、交換可能な producer が ae-framework の assurance control plane に入る経路を監査します。Raw producer output を release judgment と誤認しないための gap register であり、後続 ACP Issue が参照する安定した gap ID を定義します。

この slice は documentation / contract routing のみを対象にします。新しい production schema、adapter script、policy gate block 条件、CLI、MCP server は追加しません。

### 2. Routing inventory

| Producer class | Raw signal | Normalized judgment artifact | Schema / validator | Primary consumer | Enforcement default | Gap IDs |
| --- | --- | --- | --- | --- | --- | --- |
| Codex CLI local task | local diff summary、Issue source、validation command、task conclusion | `change-package/v2`, `claim-evidence-manifest/v1`, `ae-handoff/v1`, `hook-feedback/v1` | `schema/change-package-v2.schema.json`, `schema/claim-evidence-manifest.schema.json`, `schema/ae-handoff.schema.json`, `schema/hook-feedback.schema.json` と Contract Catalog 記載 validator | PR reviewer、`policy-gate`、PR summary、handoff | required check、risk policy、assurance profile が選ぶまで report-only | ACP-GAP-001, ACP-GAP-002 |
| Claude Code task | tool log summary、changed files、continuation note、command evidence | `ae-handoff/v1`, `hook-feedback/v1`, `change-package/v2`, optional `claim-evidence-manifest/v1` | handoff / hook-feedback / change-package / optional manifest validation | main agent、reviewer、continuation consumer | report-only。repository validation が権威ある証跡 | ACP-GAP-001, ACP-GAP-002 |
| GitHub Copilot PR review / agent | review body、inline comment、suggestion、thread state、PR diff | PR review record、`policy-decision/v1`、optional `change-package/v2`、optional `hook-feedback/v1` | review thread integrity は `pr-review-completeness`、policy decision は `schema/policy-decision-v1.schema.json` | Copilot Review Gate、reviewer、`policy-gate`、PR summary | unresolved AI review thread は block 可能。生成review本文だけでは judgment ではない | ACP-GAP-001, ACP-GAP-003, ACP-GAP-004 |
| Human maintainer | approval、rationale、manual waiver、merge decision、command evidence | `temporary-override/v1`, `policy-decision/v1`, `claim-evidence-manifest/v1`, `change-package/v2`, PR review record | `temporary-override` / `policy-decision` / manifest validation、reviewer policy、branch protection | `policy-gate`、release reviewer、audit trail | traceable waiver metadata がある場合だけ override 可能。unresolved risk は残す | ACP-GAP-001 |
| CI / test runner | required-check status、log、coverage、quality scorecard、harness health、provenance | `verify-lite-run-summary`, `quality-scorecard`, `harness-health`, `policy-input-v1`, `policy-decision/v1`, provenance sidecar | verify-lite / quality / harness / policy / provenance schemas | branch protection、PR comment、policy gate、release summary | required check は enforce。side summary は既存 policy が昇格するまで report-only | ACP-GAP-003, ACP-GAP-005 |
| Formal runner / model checker / proof tool | model/proof result、counterexample、scope、assumption | `formal-summary/v2`, compatibility `formal-summary/v1`, `assurance-summary/v1`, `claim-evidence-manifest/v1`, optional `change-package/v2` | formal summary / assurance summary / manifest validation | assurance summary、PR summary、release reviewer | scope 付き claim のみを支える。通常PRには必須化しない | ACP-GAP-003 |
| MCP tool server | TaskResponse JSON、generated spec/test/code snippet、blocked/next-action response | `TaskResponse`, `ae-handoff/v1`, `hook-feedback/v1`, 変更時は downstream `change-package/v2` | `schema/codex-task-response.schema.json`、path/approval policy、generated-artifact validation | caller、continuation consumer、main-agent reviewer | invalid tool output は reject。成功応答も review までは producer input | ACP-GAP-002, ACP-GAP-006 |
| Gemini系toolなどその他BYO coding agent | diff、comment、command transcript、tool固有raw log | vendor ではなく output type に応じて既存 artifact を選ぶ | 既存 artifact schema。この slice では vendor raw API schema を追加しない | normalized artifact 経由で reviewer / policy surface へ渡す | 既存 artifact と risk policy に接続するまで report-only | ACP-GAP-006 |

### 3. Gap register

| Gap ID | Category | Current state | Decision / next owner | Follow-up |
| --- | --- | --- | --- | --- |
| ACP-GAP-001 | missing fixture | `fixtures/agents/evidence-adapters/` に代表例はあるが、ACP rollout 用の必須producer、negative case、expected normalized artifact を明示する fixture-set manifest はない。 | bounded fixture set を追加する。fixture は example であり production contract ではない。 | ACP-011 / #3482 |
| ACP-GAP-002 | intentional preview / missing adapter | 既存 artifact の選択方針はあるが、raw producer example を読み artifact-routing request を出す report-only normalizer skeleton は未実装。 | 新しい claim state / schema を作らない非強制 skeleton を追加する。 | ACP-012 / #3483 |
| ACP-GAP-003 | missing docs / reviewer surface | verify-lite、quality scorecard、formal、assurance、PR comment に summary が分散し、producer-output gap status が reviewer 向けに統合されていない。 | Assurance Summary PR view に gap ID と missing evidence を表示する。ただし mandatory heavy lane は追加しない。 | ACP-030 / #3486 |
| ACP-GAP-004 | missing policy integration | Policy Gate と AI review gate は既にあるが、normalized agent-assurance finding を report-only policy context として消費していない。 | report-only finding を policy input / decision に渡す。enforcement は opt-in のまま維持。 | ACP-040 / #3488 |
| ACP-GAP-005 | missing validator / contract treatment | `policy-shadow-compare.v1` や一部 `artifacts/ci/*-summary.json` など、Contract Catalog 上の dedicated-schema gap が残る。 | cataloged contract debt として維持し、後続Issueがscopeするまで ACP producer routing の blocker にしない。 | Existing Contract Catalog gap list |
| ACP-GAP-006 | out of scope | 将来または外部agentの vendor-specific raw API は control-plane contract に含めない。 | output type に応じて既存 artifact に正規化し、vendor runtime coupling を避ける。 | Documented non-goal |

### 4. 運用ルール

1. Producer output は judgment の raw input であり、それ自体は judgment artifact ではありません。
2. evidence type に応じて既存 artifact を選びます。変更範囲は change package、claim は manifest、継続は handoff、blocker は hook feedback、pass/report-only/waived/block は policy decision へ接続します。
3. 新しい producer lane は、risk label、`enforce-assurance`、critical-core policy が enforcement を選ぶまで report-only から始めます。
4. この slice では mandatory raw-agent-output schema を追加しません。ACP-GAP-001 の fixture は、後続 schema Issue が明示的に変更しない限り example のままです。
5. Context Pack / Boundary Map と producer diff が矛盾する場合は、reviewable output として扱う前に設計衝突を解決します。
