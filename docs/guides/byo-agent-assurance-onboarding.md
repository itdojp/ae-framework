---
docRole: derived
canonicalSource:
- docs/product/ASSURANCE-CONTROL-PLANE-POLICY.md
- docs/product/ASSURANCE-CONTROL-PLANE.md
- docs/product/PRODUCT-FIT-INPUT-OUTPUT-TOOL-MAP.md
- docs/product/EFFECTIVENESS-METRICS.md
- docs/agents/agent-producer-matrix.md
- docs/agents/evidence-adapters.md
- docs/guides/assurance-onboarding-checklist.md
- docs/integrations/CODEX-ISSUE-RUNBOOK.md
lastVerified: '2026-06-21'
---

# BYO-Agent Assurance Onboarding Guide

> Language / 言語: English | 日本語

---

## English

This guide is the adoption path for teams that bring their own coding agent,
review bot, CI runner, formal tool, or human maintainer while keeping the
judgment-side contract inside ae-framework.

The rule is simple: **producers create changes and raw signals; ae-framework
keeps the reviewable artifacts, policy gates, and release judgment.**

Use this guide when you need to decide:

- which assurance profile to start with;
- which producer outputs are only supporting evidence;
- which summary artifact reviewers should inspect first;
- when to keep a change on the fast lane and when to escalate selected claims to
  high-assurance lanes.

Related starting points:

- Product positioning: `docs/product/ASSURANCE-CONTROL-PLANE.md`
- Canonical policy: `docs/product/ASSURANCE-CONTROL-PLANE-POLICY.md`
- Effectiveness metrics: `docs/product/EFFECTIVENESS-METRICS.md`
- 15-minute quickstart: `docs/guides/byo-agent-assurance-quickstart.md`
- Product fit and rollout profiles: `docs/product/PRODUCT-FIT-INPUT-OUTPUT-TOOL-MAP.md`
- Producer boundaries: `docs/agents/agent-producer-matrix.md`
- Raw producer routing: `docs/agents/evidence-adapters.md`
- Assurance profile checklist: `docs/guides/assurance-onboarding-checklist.md`
- Codex CLI Issue workflow: `docs/integrations/CODEX-ISSUE-RUNBOOK.md`
- Offline demo: `examples/assurance-control-plane/codex-change-package-demo/README.md`
- Quickstart demo command: `pnpm run demo:agent-assurance`

### 1. Adoption profile selection

| Profile | Start when | Minimum inputs | First outputs to review | Validation commands | Operating rule |
| --- | --- | --- | --- | --- | --- |
| Baseline | The team needs a stable daily PR gate for ordinary changes. | Repository source/tests, package manager setup, PR/Issue scope, required GitHub checks. | `verify-lite-run-summary`, report envelope, `policy-gate-summary/v1`, PR check status. | `pnpm run verify:lite`; `pnpm -s run check:schemas`; `node scripts/ci/validate-json.mjs`; required PR checks `verify-lite`, `policy-gate`, `gate`. | Start here for every repository. Producer summaries are evidence only; the required checks and policy summaries are the review surface. |
| Structured assurance | The team needs to explain which specification fragment or claim is supported by which evidence. | Context Pack, Boundary Map, assurance profile, claim refs, producer-normalization or claim-evidence inputs. | `boundary-map-summary`, `producer-normalization-summary/v1`, `assurance-summary/v1`, `claim-evidence-manifest/v1`, `change-package/v2`. | `pnpm -s run context-pack:validate`; `pnpm -s run context-pack:verify-boundary-map`; `pnpm -s run verify:assurance -- --assurance-profile <profile.json>`; optional `pnpm run producer-output:normalize -- --input <producer-output.json>`. | Keep findings report-only unless a risk label, assurance profile, or policy decision selects enforcement. |
| High-assurance critical core | A selected change touches critical claims such as authorization, payment settlement, safety, data migration, security boundary, or concurrency invariants. | `risk:high` or `enforce-assurance` rationale, critical claim set, formal/model inputs, counterexample policy, waiver metadata if needed. | `formal-summary/v2`, `assurance-summary/v1`, `claim-evidence-manifest/v1`, `policy-decision/v1`, `policy-gate-summary/v1`. | Domain-selected commands such as `pnpm run verify:formal`, `pnpm run verify:csp -- --file <model.cspm> --mode typecheck`, `pnpm -s run verify:assurance -- --assurance-profile <profile.json>`, and `node scripts/ci/enforce-assurance-summary.mjs artifacts/assurance/assurance-summary.json`. | Escalate only selected high-risk claims. Do not require heavy lanes for routine fast-lane PRs. |

### 2. Producer boundary map

| Producer | What it can produce | First ae-framework artifact to inspect | Required handling |
| --- | --- | --- | --- |
| Codex CLI local task | Local diff, command output, task summary, blocker notes. | `change-package/v2`, `producer-normalization-summary/v1`, `ae-handoff/v1`, `hook-feedback/v1`, `claim-evidence-manifest/v1` when claims are present. | Export the Issue with `scripts/codex/export-issue-task.mjs`, run the Context Pack preflight, keep `.codex-local/tasks/` uncommitted, and record missing commands in the PR. |
| Claude Code task | Diff, tool log, task response, handoff notes. | `ae-handoff/v1`, `hook-feedback/v1`, `change-package/v2`, optional `claim-evidence-manifest/v1`. | Treat tool output as producer evidence; repository validation and human/CI review remain authoritative. |
| GitHub Copilot PR review or cloud agent | PR diff, review body, inline comments, suggestions, review-thread state. | Review thread state, `policy-decision/v1`, PR summary, optional `change-package/v2`. | Run review completeness checks; unresolved AI review threads block the gate until fixed, replied to, or explicitly disposed. |
| Human maintainer | Manual review, approval, merge decision, waiver decision. | `policy-decision/v1`, `change-package/v2`, waiver entries in claim/change artifacts. | A waiver must include owner, reason, expiry, affected claim, and evidence link. Human judgment does not erase unresolved risk. |
| CI / test runner | Pass/fail, logs, coverage, verify-lite summary, report envelope. | `verify-lite-run-summary`, report envelope, `quality-scorecard`, `policy-gate-summary/v1`. | Required checks are the baseline gate. Raw logs support the decision but are not the primary review surface. |
| Formal / model / proof tool | Proof/model-check result, assumptions, counterexample, bounded-scope result. | `formal-summary/v2`, `assurance-summary/v1`, `claim-evidence-manifest/v1`. | Tool output supports only the modeled or proved scope. Counterexamples stay visible for affected claims. |

### 3. First artifacts and commands

| Question | Inspect first | Command or source |
| --- | --- | --- |
| Did the routine PR baseline pass? | `artifacts/verify-lite/verify-lite-run-summary.json` and required PR checks. | `pnpm run verify:lite` and GitHub checks `verify-lite`, `policy-gate`, `gate`. |
| Are schemas and generated artifacts contract-valid? | Contract Catalog schemas and fixture validators. | `pnpm -s run check:schemas`; `node scripts/ci/validate-json.mjs`. |
| Does the change respect Context Pack boundaries? | Boundary-map report and summary. | `pnpm -s run context-pack:validate`; `pnpm -s run context-pack:verify-boundary-map`. |
| What did the agent claim, and what evidence is missing? | `producer-normalization-summary/v1` and `assurance-summary/v1`. | `pnpm run producer-output:normalize -- --input <raw-producer-output.json>`; `pnpm -s run verify:assurance -- --assurance-profile <profile.json> --producer-summary <summary.json>`. |
| Which claims are satisfied, waived, unresolved, or high-risk? | `claim-evidence-manifest/v1`, `assurance-summary/v1`, and `policy-decision/v1`. | `pnpm -s run verify:assurance -- --assurance-profile <profile.json>` plus the PR policy-gate summary. |
| Is high-assurance enforcement justified? | Risk labels, assurance profile, formal summary, and policy-gate decision. | Apply `risk:high` / `enforce-assurance` only when the Issue or reviewer selects critical claims. |
| Can a Codex CLI Issue workflow be reproduced? | Exported task file and demo fixture. | `node scripts/codex/export-issue-task.mjs --repo <owner/repo> --issue <n> --work <repo>` and `examples/assurance-control-plane/codex-change-package-demo/README.md`. |
| Can the BYO-agent assurance flow be tried locally in 15 minutes? | Reviewer-first demo Markdown and generated summary artifacts. | `pnpm run demo:agent-assurance` and `docs/guides/byo-agent-assurance-quickstart.md`. |

### 4. Recommended rollout sequence

1. **Declare the producer boundary.** List the agents/tools that will create
   diffs or raw signals, then map each to the producer matrix.
2. **Start with Baseline.** Make `verify:lite`, schema validation, and PR
   `policy-gate` green before introducing heavier evidence lanes.
3. **Add Structured assurance only where claims need traceability.** Create an
   assurance profile, connect Context Pack claim refs, and generate
   `assurance-summary/v1` in report-only mode.
4. **Route raw producer output through existing artifacts.** Use evidence
   adapters and `producer-normalization-summary/v1`; do not create a new
   guarantee vocabulary for one agent.
5. **Escalate only selected high-risk claims.** Use `risk:high` or
   `enforce-assurance` when a specific critical-core change needs stricter
   judgment; keep ordinary PRs on the fast lane.
6. **Record reviewer evidence in the PR.** Include summary artifacts, missing
   commands, waiver rationale, review completeness status, and required-check
   status.

### 5. PR checklist for BYO-agent adoption

- [ ] Producer outputs are identified as producer evidence, not approval.
- [ ] Context Pack preflight was run or recorded as not applicable.
- [ ] Baseline commands are available: `verify:lite`, schema validation, and PR
      `policy-gate`.
- [ ] Summary artifacts are linked before raw logs.
- [ ] Missing command evidence is report-only unless policy selects enforcement.
- [ ] `risk:high` / `enforce-assurance` is used only for selected critical
      claims.
- [ ] Any waiver includes owner, reason, expiry, affected claim, and evidence
      reference.
- [ ] Codex CLI Issue work, if used, links to
      `docs/integrations/CODEX-ISSUE-RUNBOOK.md` and keeps `.codex-local/tasks/`
      out of version control.

### 6. Non-goals

- This guide does not define a hosted agent service or a sales workflow.
- This guide does not make Codex, Claude Code, Copilot, CI, or a formal tool a
  source of merge approval by itself.
- This guide does not require formal/model/proof lanes for every PR.
- This guide does not replace the schema-backed Contract Catalog.

---

## 日本語

このガイドは、任意の coding agent、review bot、CI runner、formal tool、または human maintainer を持ち込みながら、判断面の contract を ae-framework 側に残すための導入手順です。

基本ルールは明確です。**producer は変更と raw signal を生成し、ae-framework は review 可能な artifact、policy gate、release judgment を保持します。**

このガイドは次を判断するときに使います。

- どの assurance profile から始めるか。
- どの producer output を supporting evidence に留めるか。
- reviewer が最初に見る summary artifact は何か。
- いつ fast lane に留め、いつ selected claim を high-assurance lane に上げるか。

関連する入口:

- Product positioning: `docs/product/ASSURANCE-CONTROL-PLANE.md`
- Canonical policy: `docs/product/ASSURANCE-CONTROL-PLANE-POLICY.md`
- Effectiveness metrics: `docs/product/EFFECTIVENESS-METRICS.md`
- 15分 quickstart: `docs/guides/byo-agent-assurance-quickstart.md`
- Product fit / rollout profile: `docs/product/PRODUCT-FIT-INPUT-OUTPUT-TOOL-MAP.md`
- Producer boundary: `docs/agents/agent-producer-matrix.md`
- Raw producer routing: `docs/agents/evidence-adapters.md`
- Assurance profile checklist: `docs/guides/assurance-onboarding-checklist.md`
- Codex CLI Issue workflow: `docs/integrations/CODEX-ISSUE-RUNBOOK.md`
- Offline demo: `examples/assurance-control-plane/codex-change-package-demo/README.md`
- Quickstart demo command: `pnpm run demo:agent-assurance`

### 1. 導入プロファイルの選択

| Profile | 開始条件 | 最小入力 | 最初に見る出力 | Validation command | 運用ルール |
| --- | --- | --- | --- | --- | --- |
| Baseline | 通常変更に対する日常PR gateを安定させたい。 | repository source/tests、package manager setup、PR/Issue scope、required GitHub checks。 | `verify-lite-run-summary`、report envelope、`policy-gate-summary/v1`、PR check status。 | `pnpm run verify:lite`; `pnpm -s run check:schemas`; `node scripts/ci/validate-json.mjs`; required PR checks `verify-lite`, `policy-gate`, `gate`。 | 全repositoryはここから始める。producer summary は evidence であり、required check と policy summary が review surface になる。 |
| Structured assurance | どの仕様断片またはclaimが、どのevidenceで支えられるか説明したい。 | Context Pack、Boundary Map、assurance profile、claim refs、producer-normalization / claim-evidence input。 | `boundary-map-summary`、`producer-normalization-summary/v1`、`assurance-summary/v1`、`claim-evidence-manifest/v1`、`change-package/v2`。 | `pnpm -s run context-pack:validate`; `pnpm -s run context-pack:verify-boundary-map`; `pnpm -s run verify:assurance -- --assurance-profile <profile.json>`; optional `pnpm run producer-output:normalize -- --input <producer-output.json>`。 | risk label、assurance profile、policy decision が enforcement を選ぶまで report-only に留める。 |
| High-assurance critical core | authorization、payment settlement、safety、data migration、security boundary、concurrency invariant などの critical claim を変更する。 | `risk:high` / `enforce-assurance` の理由、critical claim set、formal/model input、counterexample policy、必要な waiver metadata。 | `formal-summary/v2`、`assurance-summary/v1`、`claim-evidence-manifest/v1`、`policy-decision/v1`、`policy-gate-summary/v1`。 | `pnpm run verify:formal`、`pnpm run verify:csp -- --file <model.cspm> --mode typecheck`、`pnpm -s run verify:assurance -- --assurance-profile <profile.json>`、`node scripts/ci/enforce-assurance-summary.mjs artifacts/assurance/assurance-summary.json` など、domain が選ぶ command。 | selected high-risk claim のみを昇格する。通常の fast-lane PR に heavy lane を必須化しない。 |

### 2. Producer boundary map

| Producer | 生成できるもの | 最初に見る ae-framework artifact | 必須の扱い |
| --- | --- | --- | --- |
| Codex CLI local task | Local diff、command output、task summary、blocker notes。 | `change-package/v2`、`producer-normalization-summary/v1`、`ae-handoff/v1`、`hook-feedback/v1`、claim がある場合は `claim-evidence-manifest/v1`。 | `scripts/codex/export-issue-task.mjs` で Issue を export し、Context Pack preflight を実行する。`.codex-local/tasks/` は commit せず、未実行 command は PR に記録する。 |
| Claude Code task | Diff、tool log、task response、handoff notes。 | `ae-handoff/v1`、`hook-feedback/v1`、`change-package/v2`、optional `claim-evidence-manifest/v1`。 | tool output は producer evidence。repository validation と human/CI review が authoritative evidence になる。 |
| GitHub Copilot PR review / cloud agent | PR diff、review body、inline comment、suggestion、review thread state。 | Review thread state、`policy-decision/v1`、PR summary、optional `change-package/v2`。 | review completeness を確認する。未解決AI review threadは、修正・返信・明示的dispositionまで gate を block する。 |
| Human maintainer | Manual review、approval、merge decision、waiver decision。 | `policy-decision/v1`、`change-package/v2`、claim/change artifact の waiver entry。 | waiver には owner、reason、expiry、affected claim、evidence link が必要。human judgment は unresolved risk を消さない。 |
| CI / test runner | Pass/fail、log、coverage、verify-lite summary、report envelope。 | `verify-lite-run-summary`、report envelope、`quality-scorecard`、`policy-gate-summary/v1`。 | Required checks が baseline gate。Raw log は判断を支えるが、一次review surfaceではない。 |
| Formal / model / proof tool | Proof/model-check result、assumption、counterexample、bounded-scope result。 | `formal-summary/v2`、`assurance-summary/v1`、`claim-evidence-manifest/v1`。 | tool output は modeled/proved scope だけを支える。counterexample は affected claim に残す。 |

### 3. 最初に見る artifact と command

| 問い | 最初に見るもの | Command / source |
| --- | --- | --- |
| 通常PRのbaselineは通っているか。 | `artifacts/verify-lite/verify-lite-run-summary.json` と required PR checks。 | `pnpm run verify:lite` と GitHub checks `verify-lite`, `policy-gate`, `gate`。 |
| schema と generated artifact は contract-valid か。 | Contract Catalog schema と fixture validator。 | `pnpm -s run check:schemas`; `node scripts/ci/validate-json.mjs`。 |
| 変更が Context Pack boundary を守っているか。 | Boundary-map report / summary。 | `pnpm -s run context-pack:validate`; `pnpm -s run context-pack:verify-boundary-map`。 |
| agent は何を主張し、何のevidenceが不足しているか。 | `producer-normalization-summary/v1` と `assurance-summary/v1`。 | `pnpm run producer-output:normalize -- --input <raw-producer-output.json>`; `pnpm -s run verify:assurance -- --assurance-profile <profile.json> --producer-summary <summary.json>`。 |
| どのclaimが satisfied / waived / unresolved / high-risk か。 | `claim-evidence-manifest/v1`、`assurance-summary/v1`、`policy-decision/v1`。 | `pnpm -s run verify:assurance -- --assurance-profile <profile.json>` と PR policy-gate summary。 |
| High-assurance enforcement は必要か。 | risk label、assurance profile、formal summary、policy-gate decision。 | Issue または reviewer が critical claim を選んだ場合だけ `risk:high` / `enforce-assurance` を使う。 |
| Codex CLI Issue workflow は再現できるか。 | exported task file と demo fixture。 | `node scripts/codex/export-issue-task.mjs --repo <owner/repo> --issue <n> --work <repo>` と `examples/assurance-control-plane/codex-change-package-demo/README.md`。 |
| BYO-agent assurance flow を15分で試せるか。 | reviewer-first demo Markdown と生成済み summary artifact。 | `pnpm run demo:agent-assurance` と `docs/guides/byo-agent-assurance-quickstart.md`。 |

### 4. 推奨 rollout sequence

1. **Producer boundary を宣言する。** diff や raw signal を生成する agent/tool を列挙し、producer matrix に対応付ける。
2. **Baseline から開始する。** `verify:lite`、schema validation、PR `policy-gate` を green にしてから重い evidence lane を追加する。
3. **Claim traceability が必要な場合だけ Structured assurance を追加する。** Assurance profile を作り、Context Pack claim refs を接続し、report-only の `assurance-summary/v1` を生成する。
4. **Raw producer output は既存artifactへrouteする。** Evidence adapter と `producer-normalization-summary/v1` を使い、特定agent専用の新しい保証語彙を作らない。
5. **Selected high-risk claim だけを昇格する。** 具体的な critical-core change が厳格な判断を必要とする場合に `risk:high` / `enforce-assurance` を使い、通常PRは fast lane に残す。
6. **PRにreviewer evidenceを記録する。** Summary artifact、missing command、waiver rationale、review completeness status、required-check status を残す。

### 5. BYO-agent導入PRチェックリスト

- [ ] Producer output は producer evidence として扱い、approval とは扱っていない。
- [ ] Context Pack preflight を実行した、または対象外理由を記録した。
- [ ] Baseline command（`verify:lite`、schema validation、PR `policy-gate`）を実行可能にした。
- [ ] Raw log より先に summary artifact をlinkしている。
- [ ] Missing command evidence は、policy が enforcement を選ぶまで report-only として扱っている。
- [ ] `risk:high` / `enforce-assurance` は selected critical claim に限定している。
- [ ] waiver がある場合、owner、reason、expiry、affected claim、evidence reference を持つ。
- [ ] Codex CLI Issue workflow を使う場合、`docs/integrations/CODEX-ISSUE-RUNBOOK.md` にlinkし、`.codex-local/tasks/` を version control に入れていない。

### 6. Non-goals

- この guide は hosted agent service や営業workflowを定義しません。
- Codex、Claude Code、Copilot、CI、formal tool の出力だけで merge approval とは扱いません。
- 全PRに formal/model/proof lane を要求しません。
- Schema-backed Contract Catalog を置き換えません。
