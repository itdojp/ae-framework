# Sample Issue: Codex-generated change package demo

Parent demo: #3491
Recommended worktree: `../ae-framework-demo-work`
Codex lane: `samples/docs/tests`

## Goal

Add a small reservation-audit trace to an inventory example and show how the raw
Codex CLI producer output is normalized into judgment-side evidence. This sample
Issue is intentionally small and does not require an external LLM API, hosted
agent, or GitHub Actions run.

## Producer instructions

1. Export this Issue into `.codex-local/tasks/issue-demo.md` with
   `scripts/codex/export-issue-task.mjs`.
2. Create a dedicated sibling worktree before editing code.
3. Treat Codex output as producer evidence only. Do not claim the Codex summary
   is a merge approval, proof, or policy decision.
4. Record command evidence and any missing validation in the PR body.

## Expected producer output

The raw producer output should identify:

- changed files, including the sample source, test, and documentation paths;
- focused validation commands that passed;
- broader validation that was not run by the producer;
- affected claims and whether supporting evidence is present;
- report-only gaps that the control plane should surface to reviewers.

## Acceptance criteria

- [ ] The raw producer output lists changed files and command evidence.
- [ ] The normalized summary routes to `change-package/v2`,
      `assurance-summary/v1`, and `policy-gate-summary/v1` without emitting a
      control-plane judgment.
- [ ] Missing broader validation remains visible as report-only evidence.
- [ ] The demo explains when a fast-lane change should escalate to high-risk
      assurance.

## Suggested validation commands

```bash
pnpm -s exec vitest run tests/unit/inventory/reservation-audit.test.ts --reporter dot
pnpm -s run check:doc-consistency
pnpm -s run check:schemas
```

The sample raw output intentionally marks `check:schemas` as not run by the
producer so the normalizer can demonstrate report-only missing-evidence routing.
