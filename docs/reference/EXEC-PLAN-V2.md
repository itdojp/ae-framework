---
docRole: ssot
canonicalSource:
- docs/spec/context-pack.md
- docs/reference/CONTRACT-CATALOG.md
- docs/reference/SCHEMA-GOVERNANCE.md
- policy/risk-policy.yml
lastVerified: '2026-07-01'
owner: contract-governance
verificationCommand: pnpm -s run check:doc-consistency
---

# ExecPlan v2 Reference

> Language / 言語: English | 日本語

ExecPlan v2 is a preview contract for reviewer-facing execution plans. It records the handoff between human intent, Context Pack references, task decomposition, validation commands, evidence requirements, risk policy, stop rules, rollback, and output artifacts.

It is not an orchestrator. It does not replace Context Pack, `plan-artifact/v1`, `execution-plan.v1`, or policy-gate behavior in this issue. Existing workflows continue to use their current contracts until a later migration issue explicitly changes producers and consumers.

## Contract identity

| Item | Value |
| --- | --- |
| Contract ID | `exec-plan.v2` |
| Payload version | `exec-plan/v2` |
| Schema | `schema/exec-plan.v2.schema.json` |
| Valid fixtures | `fixtures/exec-plan/baseline.exec-plan.v2.json`, `fixtures/exec-plan/structured-assurance.exec-plan.v2.json`, `fixtures/exec-plan/high-risk-selected-claims.exec-plan.v2.json` |
| Invalid fixture | `fixtures/exec-plan/invalid.missing-evidence-ref.exec-plan.v2.json` |
| Validator / renderer | `scripts/exec-plan/validate-v2.mjs` |
| Package script | `pnpm run exec-plan:v2:validate` |
| Default validation report | `artifacts/plan/exec-plan-v2-validation.json` |
| Default Markdown rendering | `artifacts/plan/exec-plan.v2.md` |
| Lifecycle | `preview` |
| Enforcement | report-only |

## Validation commands

Validate the baseline fixture and render Markdown:

```bash
pnpm run exec-plan:v2:validate
```

Validate a specific fixture:

```bash
pnpm run exec-plan:v2:validate -- \
  --file fixtures/exec-plan/structured-assurance.exec-plan.v2.json \
  --output-json artifacts/plan/exec-plan-v2-validation.json \
  --output-md artifacts/plan/exec-plan.v2.md
```

Validate every registered schema fixture through the repository registry:

```bash
node scripts/ci/validate-json.mjs
```

Expected invalid-fixture check:

```bash
node scripts/exec-plan/validate-v2.mjs \
  --file fixtures/exec-plan/invalid.missing-evidence-ref.exec-plan.v2.json \
  --no-write
```

The invalid fixture is schema-valid but semantically invalid. The validator must report the unresolved reference, for example `unknown evidence requirement id: ev.missing-contract`. This keeps fixture failures actionable for PR reviewers.

## Field model

| Field | Purpose |
| --- | --- |
| `intent` | Human-readable purpose, source Issue, references, and non-goals. |
| `scope` | In-scope / out-of-scope boundaries, target files, and affected contracts. |
| `context.contextPackRefs` | Context Pack, object, morphism, diagram, acceptance-test, or boundary-slice references. |
| `context.assuranceRefs` | Existing assurance profile, claim, and assurance-summary references. No new claim-status vocabulary is introduced. |
| `context.specKitRefs` | Optional Spec Kit spec / plan / task / contract references for interoperability bridge work. |
| `taskGraph.nodes` | Ordered execution tasks with dependencies, commands, evidence requirement refs, and output artifact refs. |
| `verificationProfile` | Fast-lane, structured-assurance, or high-assurance-selected-claims validation commands and check names. |
| `evidenceRequirements` | Evidence expected before PR review, merge judgment, release judgment, or manual approval. |
| `riskProfile` | `risk:low` / `risk:high`, human approval requirements, assurance escalation decision, and policy refs. |
| `allowedActions` | Automation actions allowed by the plan plus actions reserved for human approval. |
| `stopRules` | Conditions that halt, retry, rollback, or request human input. |
| `rollbackPlan` | Explicit rollback strategy and validation commands after rollback. |
| `outputArtifacts` | Machine-readable and Markdown artifacts expected from the plan. |

## Context Pack and assurance mapping

ExecPlan v2 composes existing control-plane evidence instead of replacing it.

| Existing concept | ExecPlan v2 location | Notes |
| --- | --- | --- |
| Context Pack object / morphism / diagram / acceptance test | `context.contextPackRefs[]` | Use `kind=object`, `morphism`, `diagram`, `acceptance-test`, or `boundary-slice`. |
| Boundary Map slice | `context.contextPackRefs[]` | Use `kind=boundary-slice` and `path=spec/context-pack/boundary-map.json`. |
| Assurance profile | `context.assuranceRefs.profiles[]` | Keep the existing profile ID. |
| Claim reference | `context.assuranceRefs.claimRefs[]` and `evidenceRequirements[].claimRefs[]` | Use existing claim IDs such as those emitted by claim-evidence manifests. |
| Assurance summary | `context.assuranceRefs.summaryArtifacts[]` / `outputArtifacts[]` | Reference `artifacts/assurance/assurance-summary.json` and `schema/assurance-summary.schema.json`. |
| Policy gate decision | `riskProfile.policyRefs[]` / `outputArtifacts[]` | Reference `policy/risk-policy.yml` and `artifacts/ci/policy-gate-summary.json`. |
| Variance input surface | `intent.sourceReferences[]` or `scope.affectedContracts[]` | Treat ExecPlan as a stable source input for variance comparison. |
| Spec Kit source artifact | `intent.sourceReferences[]` and `context.specKitRefs[]` | Use `kind=spec-kit`, `spec-kit-spec`, `spec-kit-plan`, `spec-kit-task`, or `artifact-contract` to keep Spec Kit optional and traceable. |

## Fixture roles

| Fixture | Role |
| --- | --- |
| `baseline.exec-plan.v2.json` | Normal fast-lane work with report-only contract validation and reviewer Markdown. |
| `structured-assurance.exec-plan.v2.json` | Structured assurance work that references Context Pack objects, morphisms, acceptance tests, assurance-summary, claim-evidence-manifest, and Spec Kit bridge refs. |
| `high-risk-selected-claims.exec-plan.v2.json` | Risk-escalated selected-claims work with `risk:high`, minimum human approval, policy-gate summary, selected claim evidence, and legacy-compatible `plan-artifact/v1` bridge. |
| `invalid.missing-evidence-ref.exec-plan.v2.json` | Semantic failure fixture used to verify actionable unresolved-reference messages. |
| `fixtures/spec-kit/greenfield/expected/exec-plan.v2.json` | Generated Spec Kit bridge import for a complete greenfield feature. |
| `fixtures/spec-kit/brownfield/expected/exec-plan.v2.json` | Generated Spec Kit bridge import that keeps missing/ambiguous brownfield mappings report-only. |

## Markdown rendering

`pnpm run exec-plan:v2:validate` writes a Markdown plan to `artifacts/plan/exec-plan.v2.md` when validation succeeds. The rendering is intentionally suitable for pasting into a GitHub Issue or PR body and includes:

- intent and non-goals;
- target files;
- Context Pack references;
- Spec Kit references when present;
- task graph table;
- verification commands and required checks;
- evidence requirements;
- output artifacts;
- stop rules;
- rollback steps.

When validation fails, the same `--output-md` path receives a validation error report instead of a plan rendering.

## Migration and compatibility

ExecPlan v2 is additive and preview-only in this issue.

| Existing route | Current status | ExecPlan v2 relationship |
| --- | --- | --- |
| `schema/execplan.schema.json` and `fixtures/execplan/sample.execplan.json` | legacy-compatible sample route | Kept unchanged; ExecPlan v2 uses a new filename, `schemaVersion`, and `contractId`. |
| `execution-plan.v1` from `schema/execution-plan-v1.schema.json` | automation/autopilot operation contract | Kept for PR state/action execution. ExecPlan v2 is a higher-level reviewer and evidence handoff contract. |
| `plan-artifact/v1` from `schema/plan-artifact.schema.json` | current high-risk policy-gate plan artifact | Kept as the enforced high-risk plan artifact until a later dual-read / dual-validate migration explicitly changes policy-gate. |
| Context Pack v1 | design SSOT | Referenced by ExecPlan v2; not replaced. |
| Spec Kit bridge report v1 | optional report-only interoperability artifact | Referenced by ExecPlan v2 when Spec Kit features are imported; does not make Spec Kit mandatory. |
| Assurance summary v1 and claim-evidence manifest v1 | evidence contracts | Referenced by ExecPlan v2; claim states and assurance result vocabulary remain owned by the existing contracts. |

A future migration from `plan-artifact/v1` to `exec-plan/v2` must follow `docs/reference/SCHEMA-GOVERNANCE.md` dual-write / dual-validate rules and include rollback guidance, consumer-path tests, and policy-gate impact documentation.

## Japanese summary / 日本語要約

ExecPlan v2 は、Issue の意図、Context Pack 参照、task graph、検証コマンド、evidence requirements、risk policy、stop rules、rollback、output artifacts をひとつの reviewable contract として記録する preview 契約です。agent-neutral assurance control plane の入力面を安定化するためのものであり、orchestrator 実装ではありません。現時点では `plan-artifact/v1`、`execution-plan.v1`、Context Pack、assurance-summary を置き換えず、report-only として schema / fixture / Markdown rendering / validation command を追加します。Spec Kit bridge から生成された ExecPlan v2 は `context.specKitRefs` に spec / plan / task / contract 参照を保持します。
