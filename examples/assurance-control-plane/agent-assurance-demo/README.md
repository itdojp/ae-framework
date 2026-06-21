# Agent Assurance Quickstart Demo

This example is the fixture-backed entrypoint used by
`pnpm run demo:agent-assurance` and
`docs/guides/byo-agent-assurance-quickstart.md`.

The demo is offline. It does not call an external LLM API, hosted agent service,
GitHub API, or GitHub Actions. It reuses the representative Codex CLI producer
fixture from `examples/assurance-control-plane/codex-change-package-demo/` and
writes a reviewer-first artifact set under `artifacts/`.

## Flow

```text
Codex CLI raw producer fixture
  -> producer-normalization-summary/v1
  -> assurance-summary/v1 reviewer decision surface
  -> policy-gate-summary/v1 report-only policy interpretation
  -> artifacts/review/agent-assurance-demo/assurance-review.md
```

## Run

From the repository root:

```bash
pnpm run demo:agent-assurance
```

The final reviewer surface is rendered by the reusable command:

```bash
pnpm run assurance:review-surface -- \
  --producer-summary artifacts/agents/agent-assurance-demo/producer-normalization-summary.json \
  --assurance-summary artifacts/assurance/agent-assurance-demo/assurance-summary.json \
  --policy-gate-summary artifacts/policy/agent-assurance-demo/policy-gate-summary.json \
  --verify-lite-summary artifacts/verify-lite/agent-assurance-demo/verify-lite-run-summary.json \
  --output-md artifacts/review/agent-assurance-demo/assurance-review.md
```

Default outputs:

| Artifact | Path |
| --- | --- |
| Verify Lite fixture summary | `artifacts/verify-lite/agent-assurance-demo/verify-lite-run-summary.json` |
| Producer normalization summary | `artifacts/agents/agent-assurance-demo/producer-normalization-summary.json` |
| Producer normalization Markdown | `artifacts/agents/agent-assurance-demo/producer-normalization-summary.md` |
| Assurance summary | `artifacts/assurance/agent-assurance-demo/assurance-summary.json` |
| Assurance summary Markdown | `artifacts/assurance/agent-assurance-demo/assurance-summary.md` |
| Policy summary | `artifacts/policy/agent-assurance-demo/policy-gate-summary.json` |
| Policy summary Markdown | `artifacts/policy/agent-assurance-demo/policy-gate-summary.md` |
| Reviewer surface | `artifacts/review/agent-assurance-demo/assurance-review.md` |

## Reviewer interpretation

Read `artifacts/review/agent-assurance-demo/assurance-review.md` first. The demo
uses the product effectiveness vocabulary only in demo scope:

- `missing_evidence_finding_count` is taken from the producer normalization
  summary.
- `scope_drift_finding_count` is `0` because this quickstart does not model
  scope drift.
- `reviewer_comment_count` and `ci_rerun_count` are not collected because the
  demo does not create a live PR or run GitHub Actions.
- missing Boundary Map or claim-evidence artifacts remain visible as `missing` /
  `not provided`; absence is not rendered as success.

Producer output is evidence input, not approval. The policy summary is
report-only for the ordinary fast lane; high-assurance escalation remains a
selected-claim workflow for later scenario packs.
