---
docRole: ssot
canonicalSource:
- docs/spec/context-pack.md
- docs/reference/CONTRACT-CATALOG.md
- docs/quality/CODE-QUALITY-BASELINE.md
- policy/risk-policy.yml
lastVerified: '2026-07-01'
owner: quality-maintainers
verificationCommand: pnpm -s run check:doc-consistency
---

# Variance Reduction Policy

This policy defines the report-only variance-reduction layer for repeated agent, CI, and verification runs. The goal is not byte-identical output. The goal is to make judgment-relevant differences visible after deterministic normalization.

## Variance taxonomy

| Category | Meaning | Typical source input |
| --- | --- | --- |
| `context-drift` | Context Pack or ExecPlan input changed between runs. | `context-pack`, `exec-plan` |
| `tool-version-drift` | Runtime, package manager, solver, or agent adapter version changed. | `tool-version` |
| `prompt-template-drift` | Prompt, comment, handoff, or report template changed. | `template` |
| `check-order-drift` | Validation command list, ordering, or command digest changed. | `validation-command` |
| `artifact-shape-drift` | Schema, `contractId`, `schemaVersion`, or artifact shape changed. | `artifact-contract` |
| `timestamp-noise-drift` | Time, duration, run ID, or execution attempt changed. | normalized volatile field |
| `value-drift` | Normalized judgment value changed outside the known input surfaces. | `judgment-artifact` |

## Deterministic input hashing

A variance report hashes each normalized input surface independently:

- Context Pack fingerprints (`$.inputFingerprints.contextPack`);
- ExecPlan fingerprints (`$.inputFingerprints.execPlan`);
- selected templates (`$.inputFingerprints.templates`);
- validation commands (`$.inputFingerprints.validationCommands`);
- tool versions (`$.inputFingerprints.toolVersions`);
- artifact contracts (`$.inputFingerprints.artifactContracts`).

Hashes are calculated over normalized JSON with stable key ordering. The report also hashes the full normalized judgment artifact to determine whether two runs are judgment-equivalent.

## Normalization rules

The default comparator ignores these volatile field names at any depth:

- `generatedAt`, `generatedAtUtc`, `generatedAtLocal`, `timestamp`;
- `startedAt`, `completedAt`, `durationMs`;
- `runId`, `runAttempt`.

Array order is preserved. This is intentional: check-order drift is meaningful and must not be hidden by sorting command arrays.

Operators can add a temporary allowed field with `--allowed-field <name>`, but new allowed fields must be documented when they become part of a shared workflow.

## Artifact contract

| Item | Value |
| --- | --- |
| JSON artifact | `artifacts/quality/variance-report.json` |
| Markdown artifact | `artifacts/quality/variance-report.md` |
| Schema | `schema/variance-report.schema.json` |
| Comparator | `scripts/quality/compare-judgment-artifacts.mjs` |
| Package script | `pnpm run quality:variance` |
| Fixture directory | `fixtures/variance/` |
| Enforcement mode | report-only |

Example:

```bash
pnpm run quality:variance -- \
  --baseline fixtures/variance/run-a.judgment.json \
  --candidate fixtures/variance/run-b.same-inputs.judgment.json
```

Intentional drift fixture:

```bash
pnpm run quality:variance -- \
  --baseline fixtures/variance/run-a.judgment.json \
  --candidate fixtures/variance/run-c.context-drift.judgment.json \
  --output-json artifacts/quality/variance-report.json \
  --output-md artifacts/quality/variance-report.md
```

## Report-only policy

Issue #3548 introduces a visibility layer. It does not add a required check and does not change branch protection.

A variance finding may be promoted later only when all conditions are met:

1. the compared artifact family has stable schema and fixture coverage;
2. allowed volatile fields are documented and minimal;
3. false-positive handling and exception ownership are defined;
4. a clear rollback path exists;
5. the policy-gate or workflow PR explicitly changes enforcement from report-only to blocking.

## Japanese summary / 日本語要約

この方針は、agent / CI / verification tool の出力差分を byte 一致ではなく「正規化後の judgment 差分」として比較する report-only レイヤーです。Context Pack、ExecPlan、template、validation command、tool version、artifact contract を個別にhash化し、timestamp や duration などの揺らぎは許容差分として記録します。通常PRの必須ゲートは追加しません。blocking化する場合は、別Issue/PRで schema/fixture、許容field、false positive対応、rollback、policy変更を明示します。
