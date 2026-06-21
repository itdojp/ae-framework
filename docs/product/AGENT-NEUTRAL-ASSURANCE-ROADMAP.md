---
docRole: derived
canonicalSource:
- docs/product/ASSURANCE-CONTROL-PLANE-POLICY.md
- docs/product/ASSURANCE-CONTROL-PLANE.md
- docs/spec/context-pack.md
- docs/product/EFFECTIVENESS-METRICS.md
lastVerified: '2026-06-21'
---

# Agent-Neutral Assurance Roadmap

> Language / 言語: English | 日本語

---

## English

This roadmap tracks the 90-day implementation plan for making ae-framework a stronger **BYO-agent assurance control plane**. It follows the canonical policy in `docs/product/ASSURANCE-CONTROL-PLANE-POLICY.md` and the product overview in `docs/product/ASSURANCE-CONTROL-PLANE.md`.

The first roadmap slice is scoped to GitHub Epic #3479 and child Issues #3480 through #3492. The issue bodies remain the work input for each implementation slice; this document provides the dependency map, rollout model, non-goals, and completion surfaces that keep the slices aligned. The follow-up Product effectiveness / adoption proof series starts with Epic #3507 and uses `docs/product/EFFECTIVENESS-METRICS.md` as the shared metric vocabulary before quickstart, review-surface, demo, dogfooding, fixture, and launch-kit work.

### Product thesis

Bring your own agent. Keep your assurance plane.

Codex, Claude Code, GitHub Copilot, human maintainers, CI jobs, and formal tools are replaceable **producers**. Their raw output is useful input, but it is not the trust boundary. ae-framework owns the **control plane** that normalizes raw signals into schema-backed **judgment artifacts**, PR/release summaries, and policy-gate findings.

### Effectiveness and adoption proof follow-up

Epic #3507 continues this roadmap after the control-plane foundation by proving product effectiveness and adoption readiness. The dependency sequence is:

1. #3508 defines the shared metric vocabulary in `docs/product/EFFECTIVENESS-METRICS.md`.
2. #3509 turns the vocabulary into a 15-minute BYO-agent quickstart and deterministic local demo.
3. #3510 makes PR assurance review Markdown the primary reviewer surface.
4. #3511 and #3512 add scope-drift and high-risk escalation scenarios.
5. #3514 expands cross-agent producer fixtures, #3513 aggregates dogfooding evidence in `docs/product/DOGFOODING-REPORT-2026Q3.md`, and #3515 packages the public launch kit.

The follow-up remains judgment-side: metrics evaluate review decision time, drift and missing-evidence findings, unresolved claims, policy-gate precision/recall, CI reruns, reviewer comments, and time-to-merge. It does not benchmark raw coding-agent intelligence or create new mandatory heavy lanes.

### Non-goals

This roadmap does not implement:

- a hosted agent service;
- an IDE plugin;
- a universal agent runtime;
- external LLM API calls;
- mandatory formal proof for every PR;
- a new guarantee vocabulary that bypasses existing claim, evidence, waiver, and policy contracts.

### Rollout profiles

| Profile | Default lane | Judgment artifacts | Escalation rule |
| --- | --- | --- | --- |
| Baseline | Fast lane: `verify-lite`, schema validation, `policy-gate`, `gate` | Verify Lite summary, policy decision, contract validation reports | Stays fast unless labels, risk profile, or missing required evidence select stricter review. |
| Structured assurance | Fast lane plus Context Pack, Boundary Map, producer normalization, assurance summary | Context Pack reports, boundary-map drift report, producer-normalization summary, assurance summary | Report-only by default; findings are visible without blocking ordinary PRs. |
| High-assurance critical core | Risk-based heavy lane for selected changes | Formal/model/proof summaries, waivers, proof-carrying change package, policy decision | Only `risk:high`, `enforce-assurance`, critical-core policy, or explicit assurance profile can promote missing required evidence to block/manual approval. |

### Implementation order

| Order | Issue | Priority | Scope | Depends on | Blocks | Completion surfaces |
| --- | --- | --- | --- | --- | --- | --- |
| 0 | #3479 ACP-000 | P0 | Epic and roadmap alignment. | — | #3480-#3492 | This roadmap, Epic checklist, dependency audit. |
| 1 | #3480 ACP-001 | P0 | Product positioning in README and product docs. | — | #3481, #3492 | README, product overview/policy, docs navigation. |
| 2 | #3481 ACP-010 | P0 | Contract Catalog gap audit for producer output routing. | #3480 | #3482, #3483, #3486, #3488 | Contract Catalog, producer matrix, evidence-adapter docs, gap audit report. |
| 3 | #3482 ACP-011 | P1 | Raw producer fixtures for Codex, Claude, Copilot, and human review/waiver. | #3481 | #3483, #3491 | `fixtures/agents/evidence-adapters/`, evidence-adapter mapping table. |
| 4 | #3483 ACP-012 | P1 | Report-only producer output normalizer skeleton. | #3481, #3482 | #3486, #3488, #3491 | Normalizer script, preview summary schema if added, tests, Contract Catalog entry. |
| 5 | #3484 ACP-020 | P1 | Context Pack preflight in Codex Issue workflow. | #3480 | #3485, #3490 | Codex Issue runbook, Context Pack docs, task-file template. |
| 6 | #3485 ACP-021 | P1 | Boundary Map drift detection as PR evidence. | #3484 | #3486, #3489 | Boundary-map report, PR evidence docs, validation tests. |
| 7 | #3486 ACP-030 | P1 | Assurance Summary JSON/Markdown PR surface. | #3481, #3483, #3485 | #3487, #3488, #3491 | Assurance summary schema/docs/renderer, PR summary evidence. |
| 8 | #3487 ACP-031 | P1 | Claim/evidence status UX separation. | #3486 | #3488, #3489 | Assurance model docs, fixtures/tests, status wording. |
| 9 | #3488 ACP-040 | P1 | Policy gate report-only ingestion of agent assurance findings. | #3483, #3486, #3487 | #3489, #3491 | Policy-gate summary/report-only findings, docs/tests. |
| 10 | #3489 ACP-041 | P1 | Risk escalation evidence requirements. | #3485, #3487, #3488 | #3491, #3492 | Risk policy docs/tests, label-gating docs, opt-in controls. |
| 11 | #3490 ACP-050 | P1 | Codex CLI issue export and worktree helper. | #3484 | #3491, #3492 | Codex runbook, `scripts/codex/`, PowerShell/bash examples, `.gitignore` check. |
| 12 | #3491 ACP-060 | P2 | End-to-end agent-generated change package demo. | #3482, #3483, #3486, #3488, #3489, #3490 | #3492 | Sample issue, raw/normalized fixtures, example docs/tests. |
| 13 | #3492 ACP-070 | P2 | BYO-agent assurance onboarding guide. | #3480, #3489, #3490, #3491 | — | Adoption guide, onboarding checklist, README/docs links. |

### Dependency lanes

1. **Positioning first**: #3480 fixes product language before contract and guide work reuses it.
2. **Contract routing before adapters**: #3481 defines producer-to-judgment mappings before #3482 fixtures and #3483 normalizer behavior.
3. **Preflight before runner helpers**: #3484 defines Context Pack preflight before #3485 drift evidence and #3490 worktree/task helpers.
4. **Summary before policy**: #3486 and #3487 clarify PR evidence/state display before #3488 policy-gate ingestion and #3489 escalation.
5. **Demo and adoption last**: #3491 and #3492 should only finalize after the summary, policy, and runner surfaces exist.

### Completion update surfaces

When each child Issue is completed, update the relevant surface rather than introducing a parallel status system:

| Surface | Update when |
| --- | --- |
| Epic #3479 checklist | A child Issue closes and its acceptance criteria are checked. |
| `docs/product/AGENT-NEUTRAL-ASSURANCE-ROADMAP.md` | Dependency order, scope, or completion surface changes. |
| `docs/reference/CONTRACT-CATALOG.md` | A new schema-backed judgment artifact, preview contract, producer, or consumer is added. |
| `docs/agents/evidence-adapters.md` / `docs/agents/agent-producer-matrix.md` | A producer fixture, normalizer, or raw-output routing rule changes. |
| `docs/integrations/CODEX-ISSUE-RUNBOOK.md` | Codex issue execution, preflight, worktree, or task export behavior changes. |
| `docs/product/ASSURANCE-CONTROL-PLANE-POLICY.md` | Enforcement default, risk escalation, or state vocabulary policy changes. |
| `docs/ci/*` and `policy/risk-policy.yml` | Policy-gate behavior, label semantics, or report-only/blocking conditions change. |
| `README.md` / `docs/README.md` | User-facing navigation or product positioning changes. |

### Acceptance criteria for the roadmap

- Every child Issue from #3480 through #3492 has a readable purpose, dependency, and completion surface.
- The center of the plan is judgment-side contract strengthening, not coding-agent runtime competition.
- Ordinary changes remain on the fast lane; only high-risk, `enforce-assurance`, critical-core, or explicit assurance-profile cases enter a risk-based heavy lane.
- New assurance evaluations start report-only unless an explicit policy/risk condition selects enforcement.
- The roadmap does not create new mandatory proof requirements or new claim-status vocabulary outside the current policy.

---

## 日本語

このロードマップは、ae-framework を **BYO-agent assurance control plane** として強化するための90日実装計画です。canonical policy は `docs/product/ASSURANCE-CONTROL-PLANE-POLICY.md`、product overview は `docs/product/ASSURANCE-CONTROL-PLANE.md` です。

最初の対象は GitHub Epic #3479 と子 Issue #3480〜#3492 です。各 Issue 本文を実装スライスの作業入力とし、この文書は依存関係、rollout model、非目標、完了時に更新すべき surface を固定します。後続の Product effectiveness / adoption proof series は Epic #3507 から始まり、quickstart、review surface、demo、dogfooding、fixture、launch kit の前に `docs/product/EFFECTIVENESS-METRICS.md` を共通 metric vocabulary として使います。

### Product thesis

Bring your own agent. Keep your assurance plane.

Codex、Claude Code、GitHub Copilot、人間の maintainer、CI job、formal tool は交換可能な **producer** です。raw output は有用な入力ですが、trust boundary ではありません。ae-framework は raw signal を schema-backed な **judgment artifact**、PR/release summary、policy-gate finding に正規化する **control plane** を担います。

### Effectiveness / adoption proof follow-up

Epic #3507 は control-plane foundation の後続として、product effectiveness と adoption readiness を実証します。依存順は次です。

1. #3508 で `docs/product/EFFECTIVENESS-METRICS.md` に共通 metric vocabulary を定義する。
2. #3509 で vocabulary を15分 BYO-agent quickstart と deterministic local demo に接続する。
3. #3510 で PR assurance review Markdown を reviewer が最初に見る surface にする。
4. #3511 / #3512 で scope drift と high-risk escalation scenario を追加する。
5. #3514 で cross-agent producer fixture を拡張し、#3513 で dogfooding evidence を `docs/product/DOGFOODING-REPORT-2026Q3.md` に集約し、#3515 で public launch kit にまとめる。

後続seriesも judgment-side に限定します。metric は review decision time、drift / missing-evidence finding、unresolved claim、policy-gate precision/recall、CI rerun、reviewer comment、time-to-merge を測り、raw coding-agent intelligence の benchmark や新しい mandatory heavy lane は作りません。

### 非目標

このロードマップでは次を実装しません。

- hosted agent service;
- IDE plugin;
- 汎用 agent runtime;
- 外部 LLM API 呼び出し;
- すべての PR への mandatory formal proof;
- 既存の claim、evidence、waiver、policy contract を迂回する新しい保証語彙。

### Rollout profiles

| Profile | Default lane | Judgment artifacts | Escalation rule |
| --- | --- | --- | --- |
| Baseline | Fast lane: `verify-lite`, schema validation, `policy-gate`, `gate` | Verify Lite summary, policy decision, contract validation reports | label、risk profile、missing required evidence が厳格化を選ぶまで fast lane を維持する。 |
| Structured assurance | Fast lane + Context Pack、Boundary Map、producer normalization、assurance summary | Context Pack reports、boundary-map drift report、producer-normalization summary、assurance summary | 既定は report-only。通常 PR を block せず finding を可視化する。 |
| High-assurance critical core | selected change 向けの risk-based heavy lane | formal/model/proof summaries、waiver、proof-carrying change package、policy decision | `risk:high`、`enforce-assurance`、critical-core policy、または明示的 assurance profile のみが missing required evidence を block/manual approval へ昇格できる。 |

### 実装順序

| Order | Issue | Priority | Scope | Depends on | Blocks | Completion surfaces |
| --- | --- | --- | --- | --- | --- | --- |
| 0 | #3479 ACP-000 | P0 | Epic と roadmap の整合。 | — | #3480-#3492 | この roadmap、Epic checklist、dependency audit。 |
| 1 | #3480 ACP-001 | P0 | README と product docs の product positioning。 | — | #3481, #3492 | README、product overview/policy、docs navigation。 |
| 2 | #3481 ACP-010 | P0 | producer output routing の Contract Catalog gap audit。 | #3480 | #3482, #3483, #3486, #3488 | Contract Catalog、producer matrix、evidence-adapter docs、gap audit report。 |
| 3 | #3482 ACP-011 | P1 | Codex / Claude / Copilot / human review/waiver の raw producer fixture。 | #3481 | #3483, #3491 | `fixtures/agents/evidence-adapters/`、evidence-adapter mapping table。 |
| 4 | #3483 ACP-012 | P1 | report-only producer output normalizer skeleton。 | #3481, #3482 | #3486, #3488, #3491 | normalizer script、追加時は preview summary schema、tests、Contract Catalog entry。 |
| 5 | #3484 ACP-020 | P1 | Codex Issue workflow の Context Pack preflight。 | #3480 | #3485, #3490 | Codex Issue runbook、Context Pack docs、task-file template。 |
| 6 | #3485 ACP-021 | P1 | Boundary Map drift detection を PR evidence として扱う。 | #3484 | #3486, #3489 | boundary-map report、PR evidence docs、validation tests。 |
| 7 | #3486 ACP-030 | P1 | Assurance Summary の JSON/Markdown PR surface。 | #3481, #3483, #3485 | #3487, #3488, #3491 | assurance summary schema/docs/renderer、PR summary evidence。 |
| 8 | #3487 ACP-031 | P1 | Claim/evidence status UX の分離。 | #3486 | #3488, #3489 | Assurance model docs、fixtures/tests、status wording。 |
| 9 | #3488 ACP-040 | P1 | agent assurance findings の policy-gate report-only ingestion。 | #3483, #3486, #3487 | #3489, #3491 | policy-gate summary/report-only findings、docs/tests。 |
| 10 | #3489 ACP-041 | P1 | risk escalation evidence requirements。 | #3485, #3487, #3488 | #3491, #3492 | risk policy docs/tests、label-gating docs、opt-in controls。 |
| 11 | #3490 ACP-050 | P1 | Codex CLI issue export と worktree helper。 | #3484 | #3491, #3492 | Codex runbook、`scripts/codex/`、PowerShell/bash examples、`.gitignore` check。 |
| 12 | #3491 ACP-060 | P2 | agent-generated change package demo。 | #3482, #3483, #3486, #3488, #3489, #3490 | #3492 | sample issue、raw/normalized fixtures、example docs/tests。 |
| 13 | #3492 ACP-070 | P2 | BYO-agent assurance onboarding guide。 | #3480, #3489, #3490, #3491 | — | adoption guide、onboarding checklist、README/docs links。 |

### Dependency lanes

1. **Positioning first**: #3480 で product language を固定してから contract / guide work で再利用する。
2. **Contract routing before adapters**: #3481 で producer-to-judgment mapping を定義してから #3482 fixture と #3483 normalizer を進める。
3. **Preflight before runner helpers**: #3484 で Context Pack preflight を定義してから #3485 drift evidence と #3490 worktree/task helper を整える。
4. **Summary before policy**: #3486 / #3487 で PR evidence と state 表示を整理してから #3488 policy-gate ingestion と #3489 escalation へ進む。
5. **Demo and adoption last**: #3491 / #3492 は summary、policy、runner surface が揃ってから完了させる。

### 完了時の更新 surface

子 Issue 完了時は、並行した status system を作らず、該当 surface を更新します。

| Surface | Update when |
| --- | --- |
| Epic #3479 checklist | 子 Issue が close され、acceptance criteria が checked になったとき。 |
| `docs/product/AGENT-NEUTRAL-ASSURANCE-ROADMAP.md` | dependency order、scope、completion surface が変わったとき。 |
| `docs/reference/CONTRACT-CATALOG.md` | 新しい schema-backed judgment artifact、preview contract、producer、consumer を追加したとき。 |
| `docs/agents/evidence-adapters.md` / `docs/agents/agent-producer-matrix.md` | producer fixture、normalizer、raw-output routing rule が変わったとき。 |
| `docs/integrations/CODEX-ISSUE-RUNBOOK.md` | Codex issue execution、preflight、worktree、task export behavior が変わったとき。 |
| `docs/product/ASSURANCE-CONTROL-PLANE-POLICY.md` | enforcement default、risk escalation、state vocabulary policy が変わったとき。 |
| `docs/ci/*` and `policy/risk-policy.yml` | policy-gate behavior、label semantics、report-only/blocking conditions が変わったとき。 |
| `README.md` / `docs/README.md` | user-facing navigation または product positioning が変わったとき。 |

### Roadmap acceptance criteria

- #3480〜#3492 の目的、依存関係、completion surface が読める。
- 計画の中心は coding agent runtime 競争ではなく、judgment-side contract 強化である。
- 通常変更は fast lane のままにし、high-risk、`enforce-assurance`、critical-core、明示的 assurance-profile の場合だけ risk-based heavy lane へ昇格する。
- 新しい assurance evaluation は、明示的な policy/risk 条件が enforcement を選ばない限り report-only から始める。
- 現行 policy 外の mandatory proof requirement や新しい claim-status vocabulary を導入しない。
