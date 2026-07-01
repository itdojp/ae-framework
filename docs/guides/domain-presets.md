---
docRole: ssot
lastVerified: '2026-07-01'
owner: docs-governance
verificationCommand: pnpm -s run domain-presets:render -- --preset templates/domain-presets/web-api-bff/preset.json --generated-at 2026-07-01T00:00:00.000Z --no-write
---
# Domain Assurance Presets

> Language / 言語: English | 日本語

---

## English

### 1. Purpose

Domain assurance presets package the shortest report-only starting route for product archetypes where specification and verification evidence usually has high value. They are intended to reduce onboarding work after the reference flow is stable:

1. choose the closest product archetype;
2. prepare the required inputs;
3. run the preset's starting command and verification commands;
4. attach the expected artifacts to the PR assurance review surface.

Presets do not replace Context Pack, ExecPlan v2, verification summaries, claim/evidence manifests, policy-gate decisions, or human approval. They only select the minimum useful inputs and evidence surfaces for a domain.

### 2. Report-only boundaries

| Boundary | Rule |
| --- | --- |
| Approval authority | Human maintainers remain the approval authority. A preset never approves, merges, or releases. |
| Context Pack | Every preset keeps `contextPackRequired=true`; scope and boundary conflicts still stop the flow. |
| ExecPlan | Every preset keeps `execPlanRequired=true`; tasks, validation commands, rollback, and evidence requirements remain explicit. |
| Policy gate | Presets do not add blocking policy-gate rules. Enforcement changes require a separate policy issue. |
| External APIs | Preset rendering is offline-only and does not call live external agent APIs. |
| Agent comparison | Presets evaluate ae-framework evidence routing, not coding-agent or vendor quality. |

### 3. Preset catalog

| Preset | Target user | Starting command | Primary artifacts | Escalation rule |
| --- | --- | --- | --- | --- |
| `web-api-bff` | API/BFF maintainers with HTTP contract drift or PR-quality variance | `pnpm run verify:lite` | verify-lite summary, Context Pack boundary report, ExecPlan v2, PR assurance review surface | Escalate when auth, authorization, payment, PII, cross-service contract breakage, or `risk:high` is in scope. |
| `event-driven-domain` | Inventory, ordering, payment, or workflow teams with event ordering and invariant risks | `pnpm run conformance:verify:selected-trace` | selected-trace conformance summary, generic conformance sample result, verify-lite summary, optional assurance summary | Escalate when replay is non-deterministic, invariants fail, ordering assumptions are disputed, or the domain is payment/auth/safety critical. |
| `spec-led-brownfield` | Brownfield maintainers with local Spec Kit-style feature artifacts | `pnpm run spec-kit:import-feature -- --feature-dir fixtures/spec-kit/brownfield/specs/042-inventory-modernization --output-dir artifacts/spec-kit --generated-at 2026-07-01T00:00:00.000Z` | Spec Kit bridge report, imported Context Pack, imported ExecPlan v2 | Escalate when bridge result is `fail`, a warning hides a required contract, or imported boundaries conflict with the current Context Pack. |
| `high-assurance-critical-core` | Maintainers of selected concurrency, financial, security, or protocol-critical core claims | `pnpm run verify:formal` | formal summary, claim-evidence manifest, verify-lite summary, optional policy-gate summary | Escalate when selected claims remain unresolved, formal tools are unavailable, counterexamples are found, or risk remains high after mitigation. |

### 4. When a preset is not recommended

Use the product-fit guide first when the domain is unclear: `docs/product/PRODUCT-FIT-INPUT-OUTPUT-TOOL-MAP.md`.

A domain preset is not recommended when:

- the change is a one-off PoC, short-lived script, copy-only change, or routine scaffolding with no retained evidence value;
- the project cannot run CI or retain artifacts;
- there is no Context Pack / boundary map owner for the intended slice;
- reviewers cannot identify expected output artifacts;
- the team would treat a preset output as automatic approval.

For routine CRUD-heavy changes, start with the baseline reference flow and `verify:lite` before adding a domain preset.

### 5. Local deterministic exercise

The renderer validates a local preset and emits a deterministic JSON/Markdown review surface. It is useful for onboarding and for checking that a preset can be exercised without live services.

Web API / BFF fixture:

```bash
pnpm run domain-presets:render -- \
  --preset templates/domain-presets/web-api-bff/preset.json \
  --generated-at 2026-07-01T00:00:00.000Z \
  --output-json artifacts/domain-presets/web-api-bff.json \
  --output-md artifacts/domain-presets/web-api-bff.md
```

Event-driven domain fixture:

```bash
pnpm run domain-presets:render -- \
  --preset templates/domain-presets/event-driven-domain/preset.json \
  --generated-at 2026-07-01T00:00:00.000Z \
  --output-json artifacts/domain-presets/event-driven-domain.json \
  --output-md artifacts/domain-presets/event-driven-domain.md
```

Expected deterministic outputs for these two first-slice presets are checked in under:

- `fixtures/domain-presets/web-api-bff/expected/`
- `fixtures/domain-presets/event-driven-domain/expected/`

For event-driven pilots, the first-class selected trace fixture is
`samples/conformance/sample-traces.json` by default. The preset starting command
uses `pnpm run conformance:verify:selected-trace`; `pnpm run
conformance:verify:sample` remains available as an optional generic
`configs/samples` smoke check and is not a substitute for selected-trace
evidence. When a pilot uses a different trace, record the path in ExecPlan, run
`pnpm run trace:validate -- --in <trace>`, and append `-- --in <trace>
--out <summary>` to the selected-trace conformance command.

Schema validation for all four preset templates is covered by:

```bash
node scripts/ci/validate-json.mjs
pnpm -s exec vitest run tests/scripts/domain-presets.test.ts --reporter dot
```

### 6. Interaction with Spec & Verification Kit and Spec Kit bridge

| Flow | How presets use it | Notes |
| --- | --- | --- |
| Reference flow | All presets link back to `docs/getting-started/REFERENCE-FLOW.md`. | The reference flow remains the default Issue -> Context Pack/spec input -> ExecPlan -> verification -> PR assurance path. |
| Spec & Verification Kit minimum profile | `web-api-bff`, `event-driven-domain`, and `high-assurance-critical-core` mark it as recommended when behavior can be expressed with traceable BDD/property checks. | Run `pnpm run spec-kit-min:verify` after the domain has traceable requirement IDs or `@trace:<id>` links. |
| Spec Kit bridge | `spec-led-brownfield` requires local Spec Kit-style import; other presets treat it as optional. | The bridge reads local artifacts and emits Context Pack / ExecPlan v2 candidates. It does not vendor, fork, or execute Spec Kit. |
| Loop engineering | Presets can reference loop summaries as evidence, but loop output remains report-only. | Loop evidence does not grant merge, review approval, push, or hosted-LLM authority. |
| Req2run metrics | Presets can feed adoption-readiness reporting after a run produces evidence. | Req2run metrics evaluate workflow effectiveness, not agent-vendor quality. |

### 7. Template contract

Each template lives at `templates/domain-presets/<preset>/preset.json` and conforms to `schema/domain-assurance-preset.schema.json`.
Rendered JSON evidence conforms to `schema/domain-assurance-preset-report.schema.json`.

Required template fields include:

- target user and fit classification;
- recommended and not-recommended conditions;
- required inputs and their contract references;
- starting command and default verification commands;
- expected artifacts and evidence surfaces;
- escalation rule and human-decision requirement;
- links to the reference flow and related integration docs;
- reused contracts such as `context-pack/v1`, `exec-plan/v2`, `verify-lite-run-summary/v1`, `claim-evidence-manifest/v1`, or formal/conformance summaries.

### 8. Rollout guidance

1. Start with the smallest fitting preset.
2. Confirm Context Pack and ExecPlan v2 exist before running domain-specific commands.
3. Render the preset report with a deterministic timestamp for the PR.
4. Run the preset's starting command and attach the expected evidence artifacts.
5. Use the escalation rule only when risk or missing evidence justifies a heavier lane.
6. Keep enforcement changes separate from preset adoption.

---

## 日本語

### 1. 目的

Domain assurance preset は、仕様・検証・証跡の価値が出やすい product archetype 向けに、最短の report-only 導入経路をまとめたものです。Reference flow が安定した後、次の順序で onboarding 負荷を下げるために使います。

1. 最も近い product archetype を選ぶ。
2. required input を用意する。
3. preset の starting command と verification command を実行する。
4. expected artifact を PR assurance review surface に接続する。

Preset は Context Pack、ExecPlan v2、verification summary、claim/evidence manifest、policy-gate decision、人間の approval を置き換えません。ドメインごとの最小 input と evidence surface を選ぶだけです。

### 2. report-only 境界

| 境界 | ルール |
| --- | --- |
| 承認権限 | 承認権限は human maintainer に残る。preset は approve / merge / release しない。 |
| Context Pack | すべての preset は `contextPackRequired=true`。scope / boundary conflict は flow を停止する。 |
| ExecPlan | すべての preset は `execPlanRequired=true`。task、validation command、rollback、evidence requirement は明示する。 |
| Policy gate | preset は blocking policy-gate rule を追加しない。enforcement 変更は別 policy issue で扱う。 |
| 外部API | preset renderer は offline-only で、live external agent API を呼ばない。 |
| Agent比較 | preset は ae-framework の evidence routing を扱う。coding-agent や vendor 品質の比較ではない。 |

### 3. preset catalog

| Preset | 対象 | 開始コマンド | 主な artifact | escalation |
| --- | --- | --- | --- | --- |
| `web-api-bff` | HTTP contract drift や PR 品質ばらつきがある API/BFF | `pnpm run verify:lite` | verify-lite summary、Context Pack boundary report、ExecPlan v2、PR assurance review surface | auth / authorization / payment / PII / cross-service contract breakage / `risk:high` の場合に escalation。 |
| `event-driven-domain` | event ordering や invariant risk を持つ inventory / ordering / payment / workflow | `pnpm run conformance:verify:selected-trace` | selected-trace conformance summary、generic conformance sample result、verify-lite summary、optional assurance summary | replay 非決定性、invariant failure、ordering assumption の争点化、安全重要ドメインで escalation。 |
| `spec-led-brownfield` | Spec Kit 形式または類似の local feature artifact を持つ brownfield | `pnpm run spec-kit:import-feature -- --feature-dir fixtures/spec-kit/brownfield/specs/042-inventory-modernization --output-dir artifacts/spec-kit --generated-at 2026-07-01T00:00:00.000Z` | Spec Kit bridge report、imported Context Pack、imported ExecPlan v2 | bridge result `fail`、required contract を隠す warning、既存 Context Pack との boundary conflict で escalation。 |
| `high-assurance-critical-core` | concurrency / financial / security / protocol critical な selected claim | `pnpm run verify:formal` | formal summary、claim-evidence manifest、verify-lite summary、optional policy-gate summary | claim unresolved、formal tool unavailable、counterexample、risk 残存時に escalation。 |

### 4. preset が非推奨のケース

Domain が不明な場合は、先に `docs/product/PRODUCT-FIT-INPUT-OUTPUT-TOOL-MAP.md` を確認してください。

Domain preset は次のケースでは推奨しません。

- one-off PoC、短命 script、copy-only change、routine scaffolding で、証跡保全の価値が低い。
- CI または artifact retention がない。
- 対象 slice の Context Pack / boundary map owner がいない。
- reviewer が expected output artifact を特定できない。
- team が preset output を自動 approval として扱おうとしている。

CRUD-heavy な通常変更は、domain preset を追加する前に baseline reference flow と `verify:lite` から始めます。

### 5. ローカルでの deterministic exercise

Renderer は local preset を読み取り、deterministic な JSON/Markdown review surface を生成します。live service なしで preset を試せるか確認できます。

Web API / BFF fixture:

```bash
pnpm run domain-presets:render -- \
  --preset templates/domain-presets/web-api-bff/preset.json \
  --generated-at 2026-07-01T00:00:00.000Z \
  --output-json artifacts/domain-presets/web-api-bff.json \
  --output-md artifacts/domain-presets/web-api-bff.md
```

Event-driven domain fixture:

```bash
pnpm run domain-presets:render -- \
  --preset templates/domain-presets/event-driven-domain/preset.json \
  --generated-at 2026-07-01T00:00:00.000Z \
  --output-json artifacts/domain-presets/event-driven-domain.json \
  --output-md artifacts/domain-presets/event-driven-domain.md
```

この first slice では、次の2 preset の expected deterministic output を fixture として保持します。

- `fixtures/domain-presets/web-api-bff/expected/`
- `fixtures/domain-presets/event-driven-domain/expected/`

Event-driven pilot の first-class selected trace fixture は既定で
`samples/conformance/sample-traces.json` です。preset の開始コマンドは
`pnpm run conformance:verify:selected-trace` を使います。`pnpm run
conformance:verify:sample` は optional な generic `configs/samples` smoke check
として利用可能ですが、selected-trace evidence の代替ではありません。別 trace を使う pilot は ExecPlan に path を記録し、`pnpm run trace:validate -- --in <trace>` を実行したうえで、selected-trace conformance command に `-- --in <trace> --out <summary>` を追加します。

4 preset すべての schema validation と renderer regression は次で確認します。

```bash
node scripts/ci/validate-json.mjs
pnpm -s exec vitest run tests/scripts/domain-presets.test.ts --reporter dot
```

### 6. Spec & Verification Kit / Spec Kit bridge との関係

| Flow | preset での使い方 | 補足 |
| --- | --- | --- |
| Reference flow | すべての preset が `docs/getting-started/REFERENCE-FLOW.md` に戻る。 | Issue -> Context Pack/spec input -> ExecPlan -> verification -> PR assurance の既定導線。 |
| Spec & Verification Kit minimum profile | `web-api-bff`、`event-driven-domain`、`high-assurance-critical-core` では traceable BDD/property check を書ける場合に recommended。 | requirement ID や `@trace:<id>` がある段階で `pnpm run spec-kit-min:verify` を使う。 |
| Spec Kit bridge | `spec-led-brownfield` では required。他 preset では optional。 | local artifact を読み、Context Pack / ExecPlan v2 candidate を生成する。Spec Kit を vendor / fork / execute しない。 |
| Loop engineering | loop summary を evidence として参照できるが、loop output は report-only。 | merge / review approval / push / hosted-LLM 権限は付与しない。 |
| Req2run metrics | evidence が生成された後、adoption-readiness reporting に接続できる。 | workflow effectiveness を測るもので、agent-vendor quality を比較しない。 |

### 7. template contract

各 template は `templates/domain-presets/<preset>/preset.json` に置き、`schema/domain-assurance-preset.schema.json` に準拠します。
rendered JSON evidence は `schema/domain-assurance-preset-report.schema.json` に準拠します。

主な required field は次の通りです。

- target user と fit classification;
- recommended / not-recommended condition;
- required input と contract reference;
- starting command と default verification command;
- expected artifact と evidence surface;
- escalation rule と human-decision requirement;
- reference flow と integration doc への link;
- `context-pack/v1`、`exec-plan/v2`、`verify-lite-run-summary/v1`、`claim-evidence-manifest/v1`、formal/conformance summary などの reused contract。

### 8. rollout guidance

1. 最小で適合する preset から始める。
2. domain-specific command の前に Context Pack と ExecPlan v2 があることを確認する。
3. deterministic timestamp で preset report を生成して PR に添付する。
4. preset の starting command を実行し、expected evidence artifact を接続する。
5. risk または missing evidence が重い lane を正当化する場合だけ escalation rule を使う。
6. enforcement 変更は preset 導入とは別に扱う。
