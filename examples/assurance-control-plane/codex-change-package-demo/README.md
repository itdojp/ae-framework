# Codex Change Package Assurance Demo

This example shows the smallest end-to-end path for a Codex-generated change to
become reviewable assurance evidence without trusting the Codex conclusion as a
judgment artifact.

```text
sample Issue
  -> Codex CLI raw producer output fixture
  -> producer-normalization-summary/v1
  -> assurance-summary/v1 reviewer surface
  -> policy-gate report-only findings / PR evidence
```

The demo is fixture-backed and offline. It does not call an external LLM API,
hosted agent service, or GitHub Actions. It is intended for onboarding and
regression tests only.

## Files

| Path | Role |
| --- | --- |
| `samples/codex/issues/agent-generated-change-package-demo.md` | Small sample Issue that can be exported into `.codex-local/tasks/`. |
| `producer-output/codex-cli-task-output.json` | Raw Codex CLI producer output fixture. This is not a control-plane contract. |
| `expected/producer-normalization-summary.json` | Expected report-only normalizer JSON output. |
| `expected/producer-normalization-summary.md` | Human-readable expected normalizer output. |

## Reproduce the normalizer output

From the repository root:

```bash
pnpm run producer-output:normalize -- \
  --input examples/assurance-control-plane/codex-change-package-demo/producer-output/codex-cli-task-output.json \
  --out-json artifacts/agents/codex-change-package-demo/producer-normalization-summary.json \
  --out-md artifacts/agents/codex-change-package-demo/producer-normalization-summary.md \
  --generated-at 2026-06-20T00:00:00.000Z
```

Expected generated artifacts:

- `artifacts/agents/codex-change-package-demo/producer-normalization-summary.json`
- `artifacts/agents/codex-change-package-demo/producer-normalization-summary.md`

For golden comparison, the expected files live under this example's `expected/`
directory.

## Feed the summary into the assurance review surface

The normalizer output can be supplied to the existing assurance aggregator:

```bash
pnpm -s run verify:assurance -- \
  --assurance-profile fixtures/assurance/sample.assurance-profile.json \
  --producer-summary artifacts/agents/codex-change-package-demo/producer-normalization-summary.json \
  --output-json artifacts/assurance/codex-change-package-demo/assurance-summary.json \
  --output-md artifacts/assurance/codex-change-package-demo/assurance-summary.md
```

Expected generated artifacts:

- `artifacts/assurance/codex-change-package-demo/assurance-summary.json`
- `artifacts/assurance/codex-change-package-demo/assurance-summary.md`

The assurance summary should show producer report-only findings and residual
risks. Those findings tell reviewers what still needs evidence; they do not mean
Codex approved the change.

## Policy-gate report-only interpretation

When `policy-gate` consumes `assurance-summary/v1` or
`producer-normalization-summary/v1`, missing evidence from the producer is
surfaced as report-only context for ordinary fast-lane changes. The expected
reviewer action is to inspect the missing command / claim evidence and decide
whether CI or a human review already supplied it.

Fast lane example:

- docs/tests/sample changes;
- focused unit test and doc consistency evidence present;
- broader schema validation missing in producer output but expected from CI;
- policy-gate remains report-only unless repository policy selects enforcement.

High-risk escalation example:

- payment settlement, authorization, security boundary, or critical-core data
  migration changes;
- `risk:high` or `enforce-assurance` label is selected;
- missing claim evidence may become a blocking policy decision;
- heavier lanes such as model/property/formal checks are selected only for the
  affected claims, not for every ordinary PR.

## Trust boundary

Codex CLI is a producer. Its raw output can propose claims, commands, changed
files, and open questions. ae-framework's judgment-side artifacts remain the
source of review truth:

- `producer-normalization-summary/v1` records report-only routing context;
- `change-package/v2` records reviewable change scope and evidence;
- `assurance-summary/v1` surfaces claim and producer-signal status;
- `policy-gate-summary/v1` records the policy interpretation for the PR.

Do not treat a generated task summary, successful local command, or agent text as
a merge approval or proof.
